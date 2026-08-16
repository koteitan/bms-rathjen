import Evidence.Region
import Rows.TM
import Rows.Ladder
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

/-! ## §3 THE FUNDAMENTAL SEQUENCE ON THE GENERALISED INDEX, MEASURED

§2 settled the SHAPE — one constructor, not three regions.  This section settles the
OPERATION: what `BMS.expand` is on `B`.  Measured before anything is proved, and the first
candidate is REFUTED, which is the part worth keeping.

THE POPULATION.  Every non-empty matrix in the depth-three expansion closure of the table's
52 width-two rows: **877 matrices**.  A candidate `g` is tested by the only question that
matters — `matB (g t n) 0 = BMS.expand (matB t 0) n`.

### §3.1 THE CANDIDATE THE `A` REGION SUGGESTS, AND ITS REFUTATION

`Evidence/Region.lean`'s `fsP` has three cases, and read in `B` coordinates they look like
one rule: the LAST COLUMN of a matrix is always a node with an empty argument, so either it
is `ψ₀(0)` — drop it and repeat its parent (`rep`) — or it is `ψ_w(0)` with `w ≥ 1`, and
then removing it leaves a context `C` and the sequence is `C^(n+1)(0)` (`iterOm`).  That is
`fsNaive` below.

    877 tested        421 agree        456 disagree
    52 rows tested     36 agree         16 disagree

and the 456 split into three classes, each a different reason:

    237   the last node's level is ≥ 2      the ψ₀(Ω₂) block; the rule never had a chance
     42   level ≤ 1, two or more top-level summands
    177   level ≤ 1, ONE top-level summand  — and these are matrices of the `A` region,
                                              where `Region.fs` gets them right

The two named counterexamples say what is wrong:

    ψ₀(ψ₁(ψ₂(0)))    measured  ε₀, ζ₀, Γ₀, …        naive  ε₀, ψ₀(ψ₁(ε₀)), …
    ε₀ ⊕ ψ₀(ψ₁(0))   measured  ε₀ ⊕ ψ₀(0), ε₀ ⊕ ψ₀(ψ₀(0)), …   naive re-copies the ε₀

The first says the iteration is not rooted at the top: with a level-2 leaf the copied part
starts at the `ψ₁` node, so each step nests one more `ψ₁` and the sequence climbs the Veblen
hierarchy instead of the ε one.  The second says the prefix must stay fixed.  Both are the
same mistake — `C` was taken to be the WHOLE term.

### §3.2 WHAT SURVIVES: THE BAD ROOT IS THE NEAREST ANCESTOR OF LOWER LEVEL

Let the last node be `ψ_w(0)` at depth `d`.

    w = 0, d = 0    successor — drop it (`kind` is `succ` exactly here)
    w = 0, d ≥ 1    drop it and repeat its PARENT node `n+1` times
    w ≥ 1           let `P` be the NEAREST ANCESTOR of the last node with level `< w`;
                    `D y` = `P`'s subtree with the last node replaced by `y`; the term is
                    the frame with `P`'s subtree replaced by `D^(n+1)(0)`

`Region.fs` is the case `w = 1`, where the nearest ancestor of lower level is always the
enclosing `ψ₀` — which is why all three failures above are invisible from `A`.  It is an
ANCESTOR walk and not a reverse scan of the matrix: `ψ₀(ψ₁(ψ₀(0)) ⊕ ψ₁(0))` has a level-0
column between the last node and its `ψ₀` ancestor, and the measured sequence ignores it.

MEASURED: 877 / 877 at `n ≤ 8`; 1209 / 1209 on the depth-FOUR closure of the 22 shortlisted
width-two rows; and `fsB (embed t) n = embed (fs t n)` on 183 `A`-indices, so `fsB` extends
`Region.fs` rather than competing with it.

WHAT IS NOT MEASURED HERE, and is the next piece of work: the expansion identity itself
(`BMS.expand? (matB t 0) n = some (matB (fsB t n) 0)`, the analogue of `Region.expand_mat`),
the normal form, the value, and the limit clauses.  This section fixes the TARGET of that
proof and nothing more. -/

/-- 和の連結。 -/
def appB : B → B → B
  | r, .nil => r
  | r, .nd v s a => .nd v (appB r s) a

/-- 和の最後の節を `y` で置き換える。 -/
def plugB : B → B → B
  | .nil, _ => .nil
  | .nd _ r .nil, y => appB r y
  | .nd v r a, y => .nd v r (plugB a y)

/-- 最後の節の段。 -/
def lastLvl : B → Nat
  | .nil => 0
  | .nd v _ .nil => v
  | .nd _ _ a => lastLvl a

/-- `ψ_v(P)` を `n+1` 個並べた和。 -/
def repNode (v : Nat) (P : B) : Nat → B
  | 0 => .nd v .nil P
  | k + 1 => .nd v (repNode v P k) P

/-- 段 0 の葉 (深さ ≥ 1): 落として親の節を `n+1` 個にする。 -/
def repB : B → Nat → B
  | .nil, _ => .nil
  | .nd v r a, n =>
    match a with
    | .nil => .nil
    | .nd 0 P .nil => appB r (repNode v P n)
    | _ => .nd v r (repB a n)

/-! ### §3.3 反証された候補 — 記録のために残す -/

/-- 文脈を**項全体**に取った反復。§3.1 が反証したもの。 -/
def iterTop (t : B) : Nat → B
  | 0 => plugB t .nil
  | k + 1 => plugB t (iterTop t k)

/-- **反証済み**の候補 (§3.1)。段が 2 以上、前置きのある和、そして `A` 領域の
    177 個で `BMS.expand` と食い違う。 -/
def fsNaive (t : B) (n : Nat) : B :=
  match t with
  | .nil => .nil
  | .nd v r .nil => if v == 0 then r else iterTop t n
  | .nd v r a => if lastLvl a == 0 then repB (.nd v r a) n else iterTop t n

/-! ### §3.4 生き残った規則 -/

/-- 最後の節の祖先に段が `w` 未満のものがあるか。 -/
def hasLowAnc (w : Nat) : B → Bool
  | .nil => false
  | .nd _ _ .nil => false
  | .nd v _ a => decide (v < w) || hasLowAnc w a

/-- 悪い根の部分木の反復。`D y = ψ_v(a[最後の節 := y])` として `D^(k+1)(0)`。 -/
def iterD (v : Nat) (a : B) : Nat → B
  | 0 => .nd v .nil (plugB a .nil)
  | k + 1 => .nd v .nil (plugB a (iterD v a k))

/-- 段 `w ≥ 1` の葉: 段が `w` 未満の**最も近い祖先**まで降りて、そこで反復する。 -/
def rwB (w n : Nat) : B → B
  | .nil => .nil
  | .nd v r .nil => .nd v r .nil
  | .nd v r a =>
    if hasLowAnc w a then .nd v r (rwB w n a)
    else if v < w then appB r (iterD v a n)
    else .nd v r a

/-- **一般化した基本列。** `Region.fs` の拡張 (§3.2 の測定)。 -/
def fsB : B → Nat → B
  | .nil, _ => .nil
  | .nd 0 r .nil, _ => r
  | .nd _ _ .nil, _ => .nil
  | .nd v r a, n =>
    if lastLvl a == 0 then repB (.nd v r a) n else rwB (lastLvl a) n (.nd v r a)

/-! ### §3.5 THE MEASUREMENT -/

/-- 候補 `g` が 1 点で `BMS.expand` と一致するか。復号できない行列は問わない。 -/
def agrees (g : B → Nat → B) (M : BMS.Matrix) (n : Nat) : Bool :=
  match decodeB M with
  | none => true
  | some t => matB (g t n) 0 == BMS.expand M n

/-- 母集団: 幅 2 の 52 行の深さ 3 の閉包 (空行列を除く)。 -/
def popB : List BMS.Matrix :=
  ((wideRows.flatMap fun M => cloOf M 3 3).eraseDups.filter (fun S => !S.isEmpty))

def maxLvl (S : BMS.Matrix) : Nat := (S.map (fun c => c.getD 1 0)).foldl max 0
def nTop (S : BMS.Matrix) : Nat := (S.filter (fun c => c.getD 0 0 == 0)).length
def failNaive : List BMS.Matrix :=
  popB.filter fun S => !((List.range 4).all (agrees fsNaive S))

#guard popB.length == 877
-- 反証。**除外する側の測定**であって、生き残りの確認ではない。
#guard (popB.filter fun S => (List.range 4).all (agrees fsNaive S)).length == 421
#guard failNaive.length == 456
#guard (failNaive.filter fun S => maxLvl S ≥ 2).length == 237
#guard (failNaive.filter fun S => maxLvl S ≤ 1 && nTop S ≥ 2).length == 42
#guard (failNaive.filter fun S => maxLvl S ≤ 1 && nTop S == 1).length == 177
#guard (wideRows.filter fun M => (List.range 4).all (agrees fsNaive M)).length == 36
-- 名前のついた反例 2 つ。
#guard (List.range 3).map (BMS.expand [[0,0],[1,1],[2,2]])
  == [[[0,0],[1,1]], [[0,0],[1,1],[2,1]], [[0,0],[1,1],[2,1],[3,1]]]   -- ε₀, ζ₀, Γ₀
#guard !((List.range 3).all (agrees fsNaive [[0,0],[1,1],[2,2]]))
#guard !((List.range 3).all (agrees fsNaive [[0,0],[1,1],[0,0],[1,1]]))
-- 生き残り。母集団の全部、`n <= 8` まで。
#guard popB.all fun S => (List.range 9).all (agrees fsB S)
#guard wideRows.all fun M => (List.range 9).all (agrees fsB M)
-- 深さ 4 の閉包 (選定した幅 2 の 22 行)。
#guard ((shortWide.flatMap fun M => cloOf M 3 4).eraseDups.filter
  (fun S => !S.isEmpty)).length == 1209
#guard ((shortWide.flatMap fun M => cloOf M 3 4).eraseDups).all fun S =>
  S.isEmpty || (List.range 5).all (agrees fsB S)
-- `Region.fs` の拡張であること。
def aCorpus : List A :=
  let base : List A := [.nil, .om .nil, .ps .nil .nil]
  let step (l : List A) : List A :=
    (l.flatMap fun x => l.flatMap fun y => [A.om x, A.ps x y]) ++ l
  (step (step base)).eraseDups
#guard aCorpus.length == 183
-- この行は §3.6 の `embed_fs` が定理にした。receipt として残す。
#guard aCorpus.all fun t => (List.range 5).all fun n => fsB (embed t) n == embed (fs t n)

/-! ### §3.6 `fsB` IS AN EXTENSION OF `Region.fs` — a theorem, not a guard

The last `#guard` of §3.5 is a computation on 183 closed terms; what the next region needs
to cite is an EQUATION.  Here it is:

    embed_fs : fsB (embed t) n = embed (fs t n)

so nothing already proved about the `A` region has to be re-proved.  The proof is one
induction on the index and one structural fact, `stepB_cons`: at a `ψ₀` node whose argument
is not `0`, both branches of `fsB` — `repB` and `rwB` — push the prefix straight out, which
is exactly the seam `Region.fs`'s own `app r (fsP a n)` splits along. -/

theorem embed_ne_nil : ∀ {a : A}, a ≠ .nil → ∃ v r c, embed a = .nd v r c := by
  intro a h
  cases a with
  | nil => exact absurd rfl h
  | om r => exact ⟨1, embed r, .nil, rfl⟩
  | ps r c => exact ⟨0, embed r, embed c, rfl⟩

theorem embed_app : ∀ (y x : A), embed (app x y) = appB (embed x) (embed y)
  | .nil, _ => rfl
  | .om y', x => by
    show B.nd 1 (embed (app x y')) .nil = _
    rw [embed_app y' x]; rfl
  | .ps y' c, x => by
    show B.nd 0 (embed (app x y')) (embed c) = _
    rw [embed_app y' x]; rfl

theorem repNode_rep (b : A) : ∀ n, repNode 0 (embed b) n = embed (rep b n)
  | 0 => rfl
  | k + 1 => by
    show B.nd 0 (repNode 0 (embed b) k) (embed b) = _
    rw [repNode_rep b k]; rfl

theorem iterD_iterOm (b : A) : ∀ n, iterD 0 (.nd 1 (embed b) .nil) n = embed (iterOm b n)
  | 0 => rfl
  | k + 1 => by
    show B.nd 0 .nil (plugB (.nd 1 (embed b) .nil) (iterD 0 (.nd 1 (embed b) .nil) k)) = _
    show B.nd 0 .nil (appB (embed b) (iterD 0 (.nd 1 (embed b) .nil) k)) = _
    rw [iterD_iterOm b k, ← embed_app (iterOm b k) b]
    rfl

/-- `fsB (nd 0 r a) n` の中身 (`a ≠ nil` のとき)。 -/
def stepB (r a : B) (n : Nat) : B :=
  if lastLvl a == 0 then repB (.nd 0 r a) n else rwB (lastLvl a) n (.nd 0 r a)

/-- **`stepB` は前置きを外へ出す。** -/
theorem stepB_cons (rr bb : B) (v' : Nat) (r' a' : B) (n : Nat) :
    stepB rr (.nd 0 bb (.nd v' r' a')) n = .nd 0 rr (stepB bb (.nd v' r' a') n) := by
  have hl : lastLvl (B.nd 0 bb (.nd v' r' a')) = lastLvl (B.nd v' r' a') := rfl
  show (if lastLvl (B.nd 0 bb (.nd v' r' a')) == 0 then _ else _) = _
  rw [hl]
  by_cases h0 : (lastLvl (B.nd v' r' a') == 0) = true
  · rw [if_pos h0]
    show B.nd 0 rr (repB (.nd 0 bb (.nd v' r' a')) n) = _
    show _ = B.nd 0 rr (if lastLvl (B.nd v' r' a') == 0 then _ else _)
    rw [if_pos h0]
  · rw [if_neg h0]
    have hw : ¬ (lastLvl (B.nd v' r' a') = 0) := by
      intro hc; exact h0 (by rw [hc]; rfl)
    show rwB (lastLvl (B.nd v' r' a')) n (.nd 0 rr (.nd 0 bb (.nd v' r' a'))) = _
    rw [show rwB (lastLvl (B.nd v' r' a')) n (.nd 0 rr (.nd 0 bb (.nd v' r' a')))
          = (if hasLowAnc (lastLvl (B.nd v' r' a')) (.nd 0 bb (.nd v' r' a')) then
              B.nd 0 rr (rwB (lastLvl (B.nd v' r' a')) n (.nd 0 bb (.nd v' r' a')))
            else if 0 < lastLvl (B.nd v' r' a') then
              appB rr (iterD 0 (.nd 0 bb (.nd v' r' a')) n)
            else B.nd 0 rr (.nd 0 bb (.nd v' r' a'))) from rfl,
      if_pos (show hasLowAnc (lastLvl (B.nd v' r' a')) (.nd 0 bb (.nd v' r' a')) = true from by
        show (decide (0 < lastLvl (B.nd v' r' a'))
          || hasLowAnc (lastLvl (B.nd v' r' a')) (.nd v' r' a')) = true
        rw [show decide (0 < lastLvl (B.nd v' r' a')) = true from by
          simp; omega]
        rfl)]
    show _ = B.nd 0 rr (if lastLvl (B.nd v' r' a') == 0 then _ else _)
    rw [if_neg h0]

theorem fs_ps_ne : ∀ (r a : A) (n : Nat), a ≠ .nil → fs (.ps r a) n = app r (fsP a n) := by
  intro r a n h
  cases a with
  | nil => exact absurd rfl h
  | om _ => rfl
  | ps _ _ => rfl

theorem step_fsP (n : Nat) : ∀ (a : A), a ≠ .nil → ∀ (r : B),
    stepB r (embed a) n = appB r (embed (fsP a n)) := by
  intro a
  induction a with
  | nil => intro h; exact absurd rfl h
  | om b _ =>
    intro _ r
    show (if lastLvl (B.nd 1 (embed b) .nil) == 0 then _
          else rwB (lastLvl (B.nd 1 (embed b) .nil)) n (.nd 0 r (.nd 1 (embed b) .nil))) = _
    rw [show (lastLvl (B.nd 1 (embed b) .nil) == 0) = false from rfl, if_neg (by simp),
      show lastLvl (B.nd 1 (embed b) (B.nil)) = 1 from rfl]
    show (if hasLowAnc 1 (.nd 1 (embed b) .nil) then _
          else if 0 < 1 then appB r (iterD 0 (.nd 1 (embed b) .nil) n) else _) = _
    rw [show hasLowAnc 1 (.nd 1 (embed b) (B.nil)) = false from rfl, if_neg (by simp),
      if_pos (by omega), iterD_iterOm b n]
    rfl
  | ps b c _ ihc =>
    intro _ r
    by_cases hcn : c = A.nil
    · subst hcn
      show (if lastLvl (B.nd 0 (embed b) .nil) == 0 then
              repB (.nd 0 r (.nd 0 (embed b) .nil)) n else _) = _
      rw [if_pos (show (lastLvl (B.nd 0 (embed b) (B.nil)) == 0) = true from rfl)]
      show appB r (repNode 0 (embed b) n) = _
      rw [repNode_rep b n]
      rfl
    · obtain ⟨v', r', a', hv⟩ := embed_ne_nil hcn
      have ih := ihc hcn (embed b)
      show stepB r (.nd 0 (embed b) (embed c)) n = _
      rw [hv, stepB_cons, ← hv, ih, ← embed_app (fsP c n) b, fsP_ps_ne b c n hcn]
      rfl

/-- **`fsB` は `Region.fs` の拡張である。** -/
theorem embed_fs : ∀ (t : A) (n : Nat), fsB (embed t) n = embed (fs t n) := by
  intro t n
  cases t with
  | nil => rfl
  | om r => rfl
  | ps r a =>
    by_cases ha : a = A.nil
    · subst ha; rfl
    · obtain ⟨v', r', a', hv⟩ := embed_ne_nil ha
      show fsB (.nd 0 (embed r) (embed a)) n = _
      rw [hv]
      show (if lastLvl (B.nd v' r' a') == 0 then repB (.nd 0 (embed r) (.nd v' r' a')) n
            else rwB (lastLvl (B.nd v' r' a')) n (.nd 0 (embed r) (.nd v' r' a'))) = _
      rw [show (if lastLvl (B.nd v' r' a') == 0 then repB (.nd 0 (embed r) (.nd v' r' a')) n
            else rwB (lastLvl (B.nd v' r' a')) n (.nd 0 (embed r) (.nd v' r' a')))
          = stepB (embed r) (.nd v' r' a') n from rfl, ← hv, step_fsP n a ha (embed r),
        ← embed_app (fsP a n) r, fs_ps_ne r a n ha]

/-! ## §4 THE ALGEBRA OF `matB`

`Region.lean` §2 for the generalised index.  Every proof is the same induction one
constructor shorter, because `B` has one constructor where `A` had two. -/

theorem matB_sh : ∀ (t : B) (d e : Nat), matB t (d + e) = sh e (matB t d) := by
  intro t
  induction t with
  | nil => intro d e; rfl
  | nd v r a ihr iha =>
    intro d e
    show matB r (d + e) ++ ([d + e, v] :: matB a (d + e + 1))
      = sh e (matB r d ++ ([d, v] :: matB a (d + 1)))
    rw [sh_append, ihr d e, sh_cons, shc_pair,
      show d + e + 1 = d + 1 + e from by omega, iha (d + 1) e]

theorem appB_nil : ∀ (s : B), appB .nil s = s := by
  intro s
  induction s with
  | nil => rfl
  | nd v s a ih _ => show B.nd v (appB .nil s) a = _; rw [ih]

theorem matB_app : ∀ (s r : B) (d : Nat), matB (appB r s) d = matB r d ++ matB s d := by
  intro s
  induction s with
  | nil => intro r d; exact (List.append_nil _).symm
  | nd v s a ih _ =>
    intro r d
    show matB (appB r s) d ++ ([d, v] :: matB a (d + 1))
      = matB r d ++ (matB s d ++ ([d, v] :: matB a (d + 1)))
    rw [ih r d, List.append_assoc]

theorem matB_col_len : ∀ (t : B) (d : Nat), ∀ c ∈ matB t d, c.length = 2 := by
  intro t
  induction t with
  | nil => intro d c hc; exact absurd hc (by simp [matB])
  | nd v r a ihr iha =>
    intro d c hc
    rcases List.mem_append.mp hc with h | h
    · exact ihr d c h
    · rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact iha (d + 1) c h

theorem matB_col_lb : ∀ (t : B) (d : Nat), ∀ c ∈ matB t d, d ≤ c.getD 0 0 := by
  intro t
  induction t with
  | nil => intro d c hc; exact absurd hc (by simp [matB])
  | nd v r a ihr iha =>
    intro d c hc
    rcases List.mem_append.mp hc with h | h
    · exact ihr d c h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_refl d
      · exact Nat.le_of_succ_le (iha (d + 1) c h)

/-- `ψ_v(b)` の塔。`iterD` を直接扱うより読みやすい形。 -/
def iterNode (v : Nat) (b : B) : Nat → B
  | 0 => .nd v .nil b
  | k + 1 => .nd v .nil (appB b (iterNode v b k))

theorem iterD_eq (v w : Nat) (b : B) : ∀ n,
    iterD v (.nd w b .nil) n = iterNode v b n
  | 0 => by
    show B.nd v .nil (plugB (.nd w b .nil) .nil) = _
    show B.nd v .nil (appB b .nil) = _
    rfl
  | k + 1 => by
    show B.nd v .nil (plugB (.nd w b .nil) (iterD v (.nd w b .nil) k)) = _
    show B.nd v .nil (appB b (iterD v (.nd w b .nil) k)) = _
    rw [iterD_eq v w b k]
    rfl

theorem flatten_repNode (v : Nat) (b : B) (d : Nat) : ∀ (n : Nat),
    ((List.range (n + 1)).map (fun _ => matB (.nd v .nil b) d)).flatten
      = matB (repNode v b n) d := by
  intro n
  induction n with
  | zero => show matB (.nd v .nil b) d ++ [] = _; rw [List.append_nil]; rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    show matB (repNode v b k) d ++ (matB (.nd v .nil b) d ++ [])
      = matB (repNode v b k) d ++ ([d, v] :: matB b (d + 1))
    rw [List.append_nil]
    rfl

theorem flatten_iterNode (v : Nat) (b : B) : ∀ (d n : Nat),
    ((List.range (n + 1)).map (fun m => sh m (matB (.nd v .nil b) d))).flatten
      = matB (iterNode v b n) d := by
  intro d n
  induction n generalizing d with
  | zero =>
    show sh 0 (matB (.nd v .nil b) d) ++ [] = matB (.nd v .nil b) d
    rw [List.append_nil, ← matB_sh (.nd v .nil b) d 0]
    rfl
  | succ k ih =>
    rw [flatten_range_succ]
    show sh 0 (matB (.nd v .nil b) d)
        ++ ((List.range (k + 1)).map (fun m => sh (m + 1) (matB (.nd v .nil b) d))).flatten
      = [d, v] :: matB (appB b (iterNode v b k)) (d + 1)
    rw [← matB_sh (.nd v .nil b) d 0, matB_app (iterNode v b k) b (d + 1)]
    rw [show ((List.range (k + 1)).map (fun m => sh (m + 1) (matB (.nd v .nil b) d))).flatten
        = ((List.range (k + 1)).map (fun m => sh m (matB (.nd v .nil b) (d + 1)))).flatten from by
      refine congrArg List.flatten (List.map_congr_left ?_)
      intro m _
      rw [← matB_sh (.nd v .nil b) d (m + 1), ← matB_sh (.nd v .nil b) (d + 1) m,
        show d + (m + 1) = d + 1 + m from by omega]]
    rw [ih (d + 1)]
    rfl

/-- ブロック `matB (nd v nil b) d` の性質 (`Region` の `blk_*` の一般化)。 -/
theorem blkB_root (v : Nat) (b : B) (d : Nat) : (matB (.nd v .nil b) d).getD 0 [] = [d, v] := rfl

theorem blkB_pos (v : Nat) (b : B) (d : Nat) : 0 < (matB (.nd v .nil b) d).length := by
  show 0 < ([d, v] :: matB b (d + 1)).length
  simp

theorem blkB_len2 (v : Nat) (b : B) (d : Nat) : ∀ c ∈ matB (.nd v .nil b) d, c.length = 2 :=
  matB_col_len (.nd v .nil b) d

theorem blkB_len (v : Nat) (b : B) (d : Nat) :
    (matB (.nd v .nil b) d).length = (matB b (d + 1)).length + 1 := by
  show ([d, v] :: matB b (d + 1)).length = _
  simp

theorem blkB_in (v : Nat) (b : B) (d : Nat) : ∀ i, 0 < i → i < (matB (.nd v .nil b) d).length →
    d + 1 ≤ ent (matB (.nd v .nil b) d) i 0 := by
  intro i h1 h2
  have hl := blkB_len v b d
  match i, h1 with
  | j + 1, _ =>
    have hj : j < (matB b (d + 1)).length := by omega
    show (((matB b (d + 1)).getD j []).getD 0 0) ≥ d + 1
    exact matB_col_lb b (d + 1) _ (getD_mem _ [] j hj)

/-! ## §5 THE EXPANSION IDENTITY — the two base cases and the recursion

`Region.lean` §5's three lemmas, with the level a parameter.  Its two abstract frame
lemmas needed no new proof: `expand_frame_zero` never reads the root's level at all, and
`expand_frame_one` was generalised in place to "the root's level is BELOW the last column's"
(`hvw`), which is what `t = 1` really needed.  So `Ω` was never the point — the point was
the level gap. -/

theorem matB_blk_last (v w : Nat) (b : B) (d : Nat) :
    matB (.nd v .nil (.nd w b .nil)) d = matB (.nd v .nil b) d ++ [[d + 1, w]] := by
  show [d, v] :: (matB b (d + 1) ++ ([d + 1, w] :: matB .nil (d + 2)))
    = ([d, v] :: matB b (d + 1)) ++ [[d + 1, w]]
  rfl

theorem ent_blkB_root (v : Nat) (b : B) (d : Nat) :
    ent (matB (.nd v .nil b) d) 0 0 = d := rfl

theorem ent_blkB_root1 (v : Nat) (b : B) (d : Nat) :
    ent (matB (.nd v .nil b) d) 0 1 = v := rfl

/-- **後続の底。** 引数の最後の加数が `ψ₀(0)` なら、ブロックが `n+1` 個並ぶ。 -/
theorem expand_prinB_succ (v : Nat) (b : B) (P : Matrix) (d n : Nat) :
    expand? (P ++ matB (.nd v .nil (.nd 0 b .nil)) d) n
      = some (P ++ matB (repNode v b n) d) := by
  rw [matB_blk_last v 0 b d,
    expand_frame_zero P (matB (.nd v .nil b) d) d (ent_blkB_root v b d) (blkB_in v b d)
      (blkB_len2 v b d) (blkB_pos v b d) n,
    flatten_repNode v b d n]

/-- **塔の底。** 最後の節の段 `w` が `ψ_v` の段より大きいなら、悪い根はこの節で、
    `m` 番目の複製は行 0 が一様に `m` 上がる。`Region` の Ω 塔の一般化。 -/
theorem expand_prinB_tower (v w : Nat) (hvw : v < w) (b : B) (P : Matrix) (d n : Nat) :
    expand? (P ++ matB (.nd v .nil (.nd w b .nil)) d) n
      = some (P ++ matB (iterNode v b n) d) := by
  rw [matB_blk_last v w b d,
    expand_frame_one P (matB (.nd v .nil b) d) d v w
      (ent_blkB_root v b d) (ent_blkB_root1 v b d) hvw (blkB_in v b d)
      (blkB_len2 v b d) (blkB_pos v b d) n,
    flatten_iterNode v b d n]

/-- **再帰。** 最後の節がもっと深いなら、1 段下のブロックへ落ちる。前置きに条件はない。 -/
theorem expand_prinB_deep (v w : Nat) (b c : B) (g : B) (n : Nat)
    (ih : ∀ (P : Matrix) (d : Nat),
      expand? (P ++ matB (.nd w .nil c) d) n = some (P ++ matB g d))
    (P : Matrix) (d : Nat) :
    expand? (P ++ matB (.nd v .nil (.nd w b c)) d) n
      = some (P ++ matB (.nd v .nil (appB b g)) d) := by
  have hS : P ++ matB (.nd v .nil (.nd w b c)) d
      = (P ++ matB (.nd v .nil b) d) ++ matB (.nd w .nil c) (d + 1) := by
    show P ++ ([d, v] :: (matB b (d + 1) ++ ([d + 1, w] :: matB c (d + 2))))
      = (P ++ ([d, v] :: matB b (d + 1))) ++ ([d + 1, w] :: matB c (d + 2))
    rw [List.append_assoc]
    rfl
  rw [hS, ih (P ++ matB (.nd v .nil b) d) (d + 1)]
  refine congrArg some ?_
  show (P ++ ([d, v] :: matB b (d + 1))) ++ matB g (d + 1)
    = P ++ ([d, v] :: matB (appB b g) (d + 1))
  rw [List.append_assoc, matB_app g b (d + 1)]
  rfl

/-! ## §6 `fsB` AS A SINGLE STEP

`fsB` at a `ψ_v` node whose argument is not `0` is one expression, `stepBv`, and it pushes
the prefix straight out — the seam `Region.fs`'s own `app r (fsP a n)` splits along.  That is
all §6 is; the expansion identity itself is §13, after the frame lemma the far case needs. -/

/-- 段 `v` の節に対する `fsB` の中身。 -/
def stepBv (v : Nat) (r a : B) (n : Nat) : B :=
  if lastLvl a == 0 then repB (.nd v r a) n else rwB (lastLvl a) n (.nd v r a)

theorem fsB_eq_stepBv (v : Nat) (r : B) (w : Nat) (b c : B) (n : Nat) :
    fsB (.nd v r (.nd w b c)) n = stepBv v r (.nd w b c) n := by
  cases v <;> rfl

/-- **`stepBv` は前置きを外へ出す。** -/
theorem stepBv_prefix (v : Nat) (r : B) (w : Nat) (b c : B) (n : Nat) :
    stepBv v r (.nd w b c) n = appB r (stepBv v .nil (.nd w b c) n) := by
  show (if lastLvl (B.nd w b c) == 0 then repB (.nd v r (.nd w b c)) n
        else rwB (lastLvl (B.nd w b c)) n (.nd v r (.nd w b c)))
      = appB r (if lastLvl (B.nd w b c) == 0 then repB (.nd v .nil (.nd w b c)) n
        else rwB (lastLvl (B.nd w b c)) n (.nd v .nil (.nd w b c)))
  by_cases h0 : (lastLvl (B.nd w b c) == 0) = true
  · rw [if_pos h0, if_pos h0]
    cases c with
    | nil =>
      cases w with
      | zero =>
        show appB r (repNode v b n) = appB r (appB .nil (repNode v b n))
        rw [appB_nil]
      | succ k => exact absurd h0 (by simp [lastLvl])
    | nd u b' c' => cases w <;> rfl
  · rw [if_neg h0, if_neg h0]
    have hw : ¬ (lastLvl (B.nd w b c) = 0) := by intro hc; exact h0 (by rw [hc]; rfl)
    by_cases hla : hasLowAnc (lastLvl (B.nd w b c)) (.nd w b c) = true
    · show (if hasLowAnc (lastLvl (B.nd w b c)) (.nd w b c) then
              B.nd v r (rwB (lastLvl (B.nd w b c)) n (.nd w b c)) else _)
        = appB r (if hasLowAnc (lastLvl (B.nd w b c)) (.nd w b c) then
              B.nd v .nil (rwB (lastLvl (B.nd w b c)) n (.nd w b c)) else _)
      rw [if_pos hla, if_pos hla]
      rfl
    · show (if hasLowAnc (lastLvl (B.nd w b c)) (.nd w b c) then _
            else if v < lastLvl (B.nd w b c) then
              appB r (iterD v (.nd w b c) n) else B.nd v r (.nd w b c))
        = appB r (if hasLowAnc (lastLvl (B.nd w b c)) (.nd w b c) then _
            else if v < lastLvl (B.nd w b c) then
              appB .nil (iterD v (.nd w b c) n) else B.nd v .nil (.nd w b c))
      rw [if_neg hla, if_neg hla]
      by_cases hv : v < lastLvl (B.nd w b c)
      · rw [if_pos hv, if_pos hv, appB_nil]
      · rw [if_neg hv, if_neg hv]
        rfl

/-- 最上位の加数は `ψ₀` の節でなければならない (値が `Ω` 未満)。 -/
def topOKB : B → Bool
  | .nil => true
  | .nd v r _ => (v == 0) && topOKB r
/-! ## §7 THE FAR CASE — the value side

§6 closed the case where the bad root is the last node's parent.  When it is further out,
the depth gap `e` is `lastDep a + 1` and each copy of the bad part descends by `e` rather
than by 1.  The bad part itself is the block with its last column removed, and in the index
that is `plugB a .nil` — the context with nothing in the hole.  So the whole value side is
two equations: `plugB` swaps the last COLUMN (§7's `matB_plugB`), and iterating the context
lays the copies down at depths `d, d+e, d+2e, …` (`flatten_iterD_gen`).

Nothing here is about `BMS.expand` yet; this is what the frame lemma will have to produce. -/

/-- 最後の節の (相対) 深さ。 -/
def lastDep : B → Nat
  | .nil => 0
  | .nd _ _ .nil => 0
  | .nd _ _ a => lastDep a + 1

/-- **`plugB` は最後の列を差し替える。** -/
theorem matB_plugB : ∀ (a : B), a ≠ .nil → ∀ (Y : B) (d : Nat),
    matB (plugB a Y) d = (matB a d).dropLast ++ matB Y (d + lastDep a) := by
  intro a
  induction a with
  | nil => intro h; exact absurd rfl h
  | nd u b c _ ihc =>
    intro _ Y d
    cases c with
    | nil =>
      show matB (appB b Y) d = (matB b d ++ ([d, u] :: matB .nil (d + 1))).dropLast
        ++ matB Y (d + 0)
      rw [matB_app Y b d, show matB (B.nil) (d + 1) = [] from rfl,
        show ([d, u] :: ([] : Matrix)) = [[d, u]] from rfl,
        show (matB b d ++ [[d, u]]).dropLast = matB b d from by simp,
        show d + 0 = d from rfl]
    | nd u' b' c' =>
      show matB b d ++ ([d, u] :: matB (plugB (.nd u' b' c') Y) (d + 1))
        = (matB b d ++ ([d, u] :: matB (.nd u' b' c') (d + 1))).dropLast
          ++ matB Y (d + (lastDep (.nd u' b' c') + 1))
      rw [ihc (by intro h; exact B.noConfusion h) Y (d + 1)]
      have hne : matB (B.nd u' b' c') (d + 1) ≠ [] := by
        show matB b' (d+1) ++ ([d + 1, u'] :: matB c' (d + 2)) ≠ []
        intro hc
        exact absurd (List.append_eq_nil_iff.mp hc).2 (by simp)
      rw [show (matB b d ++ ([d, u] :: matB (B.nd u' b' c') (d + 1))).dropLast
          = matB b d ++ ([d, u] :: (matB (B.nd u' b' c') (d + 1)).dropLast) from by
        rw [List.dropLast_append_of_ne_nil (by simp),
          show ([d, u] :: matB (B.nd u' b' c') (d + 1)).dropLast
            = [d, u] :: (matB (B.nd u' b' c') (d + 1)).dropLast from by
          rw [List.dropLast_cons_of_ne_nil hne]]]
      rw [List.append_assoc, show d + 1 + lastDep (B.nd u' b' c') = d + (lastDep (B.nd u' b' c') + 1)
        from by omega]
      rfl

/-- 悪い根のブロック (最後の列を落としたもの)。 -/
theorem matB_bad (v : Nat) (a : B) (ha : a ≠ .nil) (d : Nat) :
    matB (.nd v .nil (plugB a .nil)) d = [d, v] :: (matB a (d + 1)).dropLast := by
  show [d, v] :: matB (plugB a .nil) (d + 1) = _
  rw [matB_plugB a ha .nil (d + 1), show matB (B.nil) (d + 1 + lastDep a) = [] from rfl,
    List.append_nil]

/-- **深さの差が `e` の塔の行列。** `m` 番目の複製は行 0 が `m*e` 深い。 -/
theorem flatten_iterD_gen (v : Nat) (a : B) (ha : a ≠ .nil) : ∀ (d n : Nat),
    ((List.range (n + 1)).map (fun m =>
        sh (m * (lastDep a + 1)) (matB (.nd v .nil (plugB a .nil)) d))).flatten
      = matB (iterD v a n) d := by
  intro d n
  induction n generalizing d with
  | zero =>
    rw [show (List.range (0 + 1)) = [0] from rfl]
    show sh (0 * (lastDep a + 1)) (matB (.nd v .nil (plugB a .nil)) d) ++ [] = _
    rw [List.append_nil, show 0 * (lastDep a + 1) = 0 from by omega,
      ← matB_sh (.nd v .nil (plugB a .nil)) d 0]
    rfl
  | succ k ih =>
    rw [flatten_range_succ]
    show sh (0 * (lastDep a + 1)) (matB (.nd v .nil (plugB a .nil)) d)
        ++ ((List.range (k + 1)).map (fun m =>
             sh ((m + 1) * (lastDep a + 1)) (matB (.nd v .nil (plugB a .nil)) d))).flatten
      = matB (.nd v .nil (plugB a (iterD v a k))) d
    rw [show 0 * (lastDep a + 1) = 0 from by omega,
      ← matB_sh (.nd v .nil (plugB a .nil)) d 0,
      show ((List.range (k + 1)).map (fun m =>
             sh ((m + 1) * (lastDep a + 1)) (matB (.nd v .nil (plugB a .nil)) d))).flatten
        = ((List.range (k + 1)).map (fun m =>
             sh (m * (lastDep a + 1))
               (matB (.nd v .nil (plugB a .nil)) (d + (lastDep a + 1))))).flatten from by
      refine congrArg List.flatten (List.map_congr_left ?_)
      intro m _
      rw [← matB_sh (.nd v .nil (plugB a .nil)) d ((m + 1) * (lastDep a + 1)),
        ← matB_sh (.nd v .nil (plugB a .nil)) (d + (lastDep a + 1)) (m * (lastDep a + 1)),
        show d + (m + 1) * (lastDep a + 1) = d + (lastDep a + 1) + m * (lastDep a + 1)
          from by rw [Nat.succ_mul]; omega],
      ih (d + (lastDep a + 1))]
    show matB (.nd v .nil (plugB a .nil)) d ++ matB (iterD v a k) (d + (lastDep a + 1)) = _
    rw [matB_bad v a ha d]
    show [d, v] :: (matB a (d + 1)).dropLast ++ matB (iterD v a k) (d + (lastDep a + 1))
      = [d, v] :: matB (plugB a (iterD v a k)) (d + 1)
    rw [matB_plugB a ha (iterD v a k) (d + 1),
      show d + 1 + lastDep a = d + (lastDep a + 1) from by omega]
    rfl

/-! ## §8 THE ROW-0 PARENT CHAIN IS THE LEFT-MINIMA

This is the ingredient §6 did not need and the far case cannot do without.  `Region.lean`'s
`frame_parent0` places the row-0 bad root at the block's own root, and that is true only
because the last column sits at depth `d + 1` — one step, no chain.  With a gap the chain has
interior steps, and the row-1 bad root is the largest chain element of level below the last
node's.  So the chain has to be characterised, not just reached.

    q ∈ iterParent (parent M 0) fuel x  ↔  q < x ∧ every column in (q, x] is DEEPER than q

`parent M 0` takes the maximum earlier column with a smaller row-0 entry, so following it is
scanning leftward and updating the depth record — and the set of records is exactly the set
of left-minima.  On a `matB` matrix those are the tree ANCESTORS of the last node, which is
why §3.2's rule is an ancestor walk; turning that into the level condition is the next step. -/

/-- `q` は `x` から見て**左極小** — `q` より右で `x` まではすべて `q` より深い。 -/
def LMin (M : Matrix) (q x : Nat) : Prop :=
  q < x ∧ ∀ p, q < p → p ≤ x → ent M q 0 < ent M p 0

/-- **行 0 の親鎖は左極小の列そのもの。** BMS の `parent` は「より浅い最大の列」なので、
    鎖をたどることは左へ走査して深さの記録を更新することに等しい。 -/
theorem mem_iterParent0 (M : Matrix) : ∀ (fuel x q : Nat), x ≤ fuel →
    (q ∈ iterParent (parent M 0) fuel x ↔ LMin M q x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x q hx
    constructor
    · intro h; exact absurd h (by simp [iterParent])
    · rintro ⟨h1, h2⟩; omega
  | succ g ih =>
    intro x q hx
    cases hr : parent M 0 x with
    | none =>
      constructor
      · intro h; rw [iterParent_nil hr] at h; exact absurd h (by simp)
      · rintro ⟨h1, h2⟩
        exfalso
        have hq : q ∈ (List.range x).filter (fun p => decide (ent M p 0 < ent M x 0)) :=
          List.mem_filter.mpr ⟨List.mem_range.mpr h1,
            decide_eq_true (h2 x h1 (Nat.le_refl x))⟩
        have : ((List.range x).filter (fun p => decide (ent M p 0 < ent M x 0))) = [] :=
          List.max?_eq_none_iff.mp hr
        rw [this] at hq
        exact absurd hq (by simp)
    | some r =>
      obtain ⟨hrm, hrmax⟩ := List.max?_eq_some_iff.mp hr
      rw [List.mem_filter, List.mem_range] at hrm
      have hrx : r < x := hrm.1
      have hrlt : ent M r 0 < ent M x 0 := of_decide_eq_true hrm.2
      have hgap : ∀ p, r < p → p < x → ent M x 0 ≤ ent M p 0 := by
        intro p h1 h2
        rcases Nat.lt_or_ge (ent M p 0) (ent M x 0) with hc | hc
        · exfalso
          have hmem : p ∈ (List.range x).filter (fun p => decide (ent M p 0 < ent M x 0)) :=
            List.mem_filter.mpr ⟨List.mem_range.mpr h2, decide_eq_true hc⟩
          have := hrmax p hmem
          omega
        · exact hc
      rw [iterParent_cons hr]
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · refine ⟨hrx, ?_⟩
          intro p h1 h2
          rcases Nat.lt_or_ge p x with hp | hp
          · have := hgap p h1 hp; omega
          · have : p = x := by omega
            subst this; exact hrlt
        · obtain ⟨g1, g2⟩ := (ih r q (by omega)).mp h
          refine ⟨by omega, ?_⟩
          intro p h1 h2
          rcases Nat.lt_or_ge r p with hp | hp
          · have hqr : ent M q 0 < ent M r 0 := g2 r g1 (Nat.le_refl r)
            rcases Nat.lt_or_ge p x with hp2 | hp2
            · have := hgap p hp hp2; omega
            · have : p = x := by omega
              subst this; omega
          · exact g2 p h1 hp
      · rintro ⟨h1, h2⟩
        have hqf : q ∈ (List.range x).filter (fun p => decide (ent M p 0 < ent M x 0)) :=
          List.mem_filter.mpr ⟨List.mem_range.mpr h1,
            decide_eq_true (h2 x h1 (Nat.le_refl x))⟩
        have hqr : q ≤ r := hrmax q hqf
        rcases Nat.eq_or_lt_of_le hqr with rfl | hlt
        · exact List.mem_cons_self
        · refine List.mem_cons_of_mem _ ((ih r q (by omega)).mpr ⟨hlt, ?_⟩)
          intro p hp1 hp2
          exact h2 p hp1 (by omega)

/-! ## §9 LEFT-MINIMA INSIDE A BLOCK ARE ANCESTORS, AND THEIR LEVELS

§8 says the chain is the left-minima; this says what the left-minima of a `matB` block are.
The induction is the same three-way split every proof in this file makes — inside the
prefix, at the node, inside the argument — and the first case is VACUOUS: a column of the
prefix cannot be a left-minimum of anything past the node, because the node sits at depth
`d` and the prefix does not go above `d`.  So the left-minima are exactly the ancestors of
the last node, and `hasLowAnc w a = false` is precisely "no ancestor has level below `w`". -/

theorem ent_append_left (P Q : Matrix) (j y : Nat) (h : j < P.length) :
    ent (P ++ Q) j y = ent P j y := by
  show ((P ++ Q).getD j []).getD y 0 = _
  rw [show (P ++ Q).getD j [] = P.getD j [] from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]]
  rfl

theorem matB_len_pos : ∀ (a : B) (d : Nat), a ≠ .nil → 0 < (matB a d).length := by
  intro a d h
  cases a with
  | nil => exact absurd rfl h
  | nd u b c =>
    show 0 < (matB b d ++ ([d, u] :: matB c (d + 1))).length
    rw [List.length_append, List.length_cons]
    omega

theorem anc_lvl : ∀ (a : B), a ≠ .nil → hasLowAnc (lastLvl a) a = false → ∀ (d : Nat),
    ∀ j, j < (matB a d).length - 1 →
      (∀ p, j < p → p ≤ (matB a d).length - 1 →
        ent (matB a d) j 0 < ent (matB a d) p 0) →
      lastLvl a ≤ ent (matB a d) j 1 := by
  intro a
  induction a with
  | nil => intro h; exact absurd rfl h
  | nd u b c _ ihc =>
    intro _ hlow d j hj hmin
    have hXeq : matB (B.nd u b c) d = matB b d ++ ([d, u] :: matB c (d + 1)) := rfl
    have hlenX : (matB (B.nd u b c) d).length
        = (matB b d).length + ((matB c (d + 1)).length + 1) := by
      rw [hXeq, List.length_append, List.length_cons]
    have hentnb : ∀ y, ent (matB (B.nd u b c) d) (matB b d).length y
        = ([d, u] : Col).getD y 0 := by
      intro y
      rw [hXeq, ent_append (matB b d) _ _ y (Nat.le_refl _),
        show (matB b d).length - (matB b d).length = 0 from by omega]
      rfl
    have hlow_j : ∀ i, i < (matB b d).length →
        i < (matB (B.nd u b c) d).length - 1 →
        (∀ p, i < p → p ≤ (matB (B.nd u b c) d).length - 1 →
          ent (matB (B.nd u b c) d) i 0 < ent (matB (B.nd u b c) d) p 0) → False := by
      intro i hi _ hm
      have hnbLE : (matB b d).length ≤ (matB (B.nd u b c) d).length - 1 := by
        rw [hlenX]; omega
      have h1 := hm (matB b d).length hi hnbLE
      rw [hentnb 0, show ([d, u] : Col).getD 0 0 = d from rfl,
        hXeq, ent_append_left (matB b d) _ i 0 hi] at h1
      have h2 : d ≤ ent (matB b d) i 0 :=
        matB_col_lb b d _ (getD_mem (matB b d) [] i hi)
      omega
    cases c with
    | nil =>
      refine absurd (hlow_j j ?_ hj hmin) (by simp)
      rw [hlenX, show (matB (B.nil) (d + 1)).length = 0 from rfl] at hj
      omega
    | nd u' b' c' =>
      rcases Nat.lt_trichotomy j (matB b d).length with hlt | heq | hgt
      · exact absurd (hlow_j j hlt hj hmin) (by simp)
      · subst heq
        have hle : lastLvl (B.nd u' b' c') ≤ u := by
          have hb : (decide (u < lastLvl (B.nd u' b' c'))
            || hasLowAnc (lastLvl (B.nd u' b' c')) (.nd u' b' c')) = false := hlow
          have h1 : decide (u < lastLvl (B.nd u' b' c')) = false := by
            cases hd : decide (u < lastLvl (B.nd u' b' c')) with
            | false => rfl
            | true => rw [hd] at hb; exact absurd hb (by simp)
          have := of_decide_eq_false h1
          omega
        rw [hentnb 1, show ([d, u] : Col).getD 1 0 = u from rfl]
        exact hle
      · have hYpos : 0 < (matB (B.nd u' b' c') (d + 1)).length :=
          matB_len_pos _ _ (by intro h; exact B.noConfusion h)
        have hsplit : matB (B.nd u b c') d = matB (B.nd u b c') d := rfl
        have hentX : ∀ i y, (matB b d).length + 1 ≤ i →
            ent (matB (B.nd u b (.nd u' b' c')) d) i y
              = ent (matB (B.nd u' b' c') (d + 1)) (i - ((matB b d).length + 1)) y := by
          intro i y hi
          have hs : matB (B.nd u b (.nd u' b' c')) d
              = (matB b d ++ [[d, u]]) ++ matB (B.nd u' b' c') (d + 1) := by
            rw [List.append_assoc]; rfl
          have hp : (matB b d ++ [[d, u]]).length = (matB b d).length + 1 := by
            rw [List.length_append]; simp
          rw [hs, ent_append _ _ i y (by rw [hp]; exact hi), hp]
        have hjb : (matB b d).length + 1 ≤ j := by omega
        have hlenXY : (matB (B.nd u b (.nd u' b' c')) d).length - 1
            = (matB b d).length + (matB (B.nd u' b' c') (d + 1)).length := by
          rw [hlenX]; omega
        have hlow' : hasLowAnc (lastLvl (B.nd u' b' c')) (.nd u' b' c') = false := by
          have hb : (decide (u < lastLvl (B.nd u' b' c'))
            || hasLowAnc (lastLvl (B.nd u' b' c')) (.nd u' b' c')) = false := hlow
          cases hd : hasLowAnc (lastLvl (B.nd u' b' c')) (B.nd u' b' c') with
          | false => rfl
          | true => rw [hd] at hb; exact absurd hb (by simp)
        have key := ihc (by intro h; exact B.noConfusion h) hlow' (d + 1)
          (j - ((matB b d).length + 1))
          (by rw [hlenXY] at hj; omega)
          (by
            intro p hp1 hp2
            have hp : p + ((matB b d).length + 1)
                ≤ (matB (B.nd u b (.nd u' b' c')) d).length - 1 := by
              rw [hlenXY]; omega
            have hh := hmin (p + ((matB b d).length + 1)) (by omega) hp
            rw [hentX j 0 hjb, hentX (p + ((matB b d).length + 1)) 0 (by omega),
              show p + ((matB b d).length + 1) - ((matB b d).length + 1) = p from by omega] at hh
            exact hh)
        rw [hentX j 1 hjb]
        exact key

/-! ## §10 SPLITTING THE BLOCK OFF ITS LAST COLUMN

`plugB a .nil` removes the last node, and putting `ψ_(lastLvl a)(0)` back gives `a` again —
so the block is its bad part followed by one column, `[d + 1 + lastDep a, lastLvl a]`.  That
is the `Bk ++ [last]` shape the frame lemmas consume. -/

theorem plugB_last : ∀ (a : B), a ≠ .nil → plugB a (.nd (lastLvl a) .nil .nil) = a := by
  intro a
  induction a with
  | nil => intro h; exact absurd rfl h
  | nd u b c _ ihc =>
    intro _
    cases c with
    | nil =>
      show appB b (.nd u .nil .nil) = _
      rfl
    | nd u' b' c' =>
      show B.nd u b (plugB (.nd u' b' c') (.nd (lastLvl (B.nd u' b' c')) .nil .nil)) = _
      rw [ihc (by intro h; exact B.noConfusion h)]

theorem matB_last : ∀ (a : B), a ≠ .nil → ∀ (d : Nat),
    matB a d = (matB a d).dropLast ++ [[d + lastDep a, lastLvl a]] := by
  intro a ha d
  have h := matB_plugB a ha (.nd (lastLvl a) .nil .nil) d
  rw [plugB_last a ha] at h
  rw [show matB (B.nd (lastLvl a) .nil .nil) (d + lastDep a)
      = [[d + lastDep a, lastLvl a]] from rfl] at h
  exact h

/-- **ブロックは「悪い部分」と最後の列に割れる。** -/
theorem matB_split (v : Nat) (a : B) (ha : a ≠ .nil) (d : Nat) :
    matB (.nd v .nil a) d
      = matB (.nd v .nil (plugB a .nil)) d ++ [[d + 1 + lastDep a, lastLvl a]] := by
  rw [matB_bad v a ha d]
  show [d, v] :: matB a (d + 1) = ([d, v] :: (matB a (d + 1)).dropLast) ++ _
  rw [show ([d, v] :: (matB a (d + 1)).dropLast) ++ [[d + 1 + lastDep a, lastLvl a]]
      = [d, v] :: ((matB a (d + 1)).dropLast ++ [[d + 1 + lastDep a, lastLvl a]]) from rfl,
    ← matB_last a ha (d + 1)]

/-! ## §11 THE FRAME LEMMA AT GAP `e`

`Region.lean`'s `expand_frame_one` is the case `e = 1`, where `frame_parent0` settles the
row-0 bad root in one step.  Here the gap is arbitrary and the chain has interior elements,
so the row-1 bad root is found by §8 and §9 instead: the root is a left-minimum of every
later index (hence in the chain, and its level is below the last column's), and every OTHER
chain element has level at least the last column's (that is the caller's `hanc`).  So the
maximum of the filtered chain is the root, and `delta` on row 0 is `e` — the `m`-th copy
descends by `m·e`. -/

theorem expand_frame_gap (P Bk : Matrix) (d v w e : Nat)
    (hroot0 : ent Bk 0 0 = d) (hroot1 : ent Bk 0 1 = v) (hvw : v < w) (he : 1 ≤ e)
    (hin : ∀ i, 0 < i → i < Bk.length → d + 1 ≤ ent Bk i 0)
    (hlen2 : ∀ c ∈ Bk, c.length = 2) (hk : 0 < Bk.length)
    (hanc : ∀ q, P.length < q → q < P.length + Bk.length →
      LMin (P ++ (Bk ++ [[d + e, w]])) q (P.length + Bk.length) →
      w ≤ ent (P ++ (Bk ++ [[d + e, w]])) q 1)
    (n : Nat) :
    expand? (P ++ (Bk ++ [[d + e, w]])) n
      = some (P ++ ((List.range (n + 1)).map (fun m => sh (m * e) Bk)).flatten) := by
  have hlen := frame_len P Bk [d + e, w]
  have hP0 : ent (P ++ (Bk ++ [[d + e, w]])) P.length 0 = d := by
    rw [show P.length = P.length + 0 from by omega, frame_ent P Bk [d + e, w] 0 0 hk]
    exact hroot0
  have hP1 : ent (P ++ (Bk ++ [[d + e, w]])) P.length 1 = v := by
    rw [show P.length = P.length + 0 from by omega, frame_ent P Bk [d + e, w] 0 1 hk]
    exact hroot1
  have hL0 : ent (P ++ (Bk ++ [[d + e, w]])) (P.length + Bk.length) 0 = d + e :=
    frame_ent_last P Bk [d + e, w] 0
  have hL1 : ent (P ++ (Bk ++ [[d + e, w]])) (P.length + Bk.length) 1 = w :=
    frame_ent_last P Bk [d + e, w] 1
  have hroot : ∀ x, P.length < x → x ≤ P.length + Bk.length →
      LMin (P ++ (Bk ++ [[d + e, w]])) P.length x := by
    intro x h1 h2
    refine ⟨h1, ?_⟩
    intro p hp1 hp2
    rw [hP0]
    rcases Nat.lt_or_ge p (P.length + Bk.length) with hp | hp
    · have hi : p - P.length < Bk.length := by omega
      have hge := hin (p - P.length) (by omega) hi
      rw [show p = P.length + (p - P.length) from by omega,
        frame_ent P Bk [d + e, w] (p - P.length) 0 hi]
      omega
    · rw [show p = P.length + Bk.length from by omega, hL0]
      omega
  have hchain : ∀ x, P.length < x → x ≤ P.length + Bk.length →
      P.length ∈ iterParent (parent (P ++ (Bk ++ [[d + e, w]])) 0) x x :=
    fun x h1 h2 => (mem_iterParent0 _ x x P.length (Nat.le_refl x)).mpr (hroot x h1 h2)
  have hp1 : parent (P ++ (Bk ++ [[d + e, w]])) 1 (P.length + Bk.length) = some P.length := by
    show ((iterParent (parent (P ++ (Bk ++ [[d + e, w]])) 0)
        (P.length + Bk.length) (P.length + Bk.length)).filter
        (fun q => decide (ent (P ++ (Bk ++ [[d + e, w]])) q 1
          < ent (P ++ (Bk ++ [[d + e, w]])) (P.length + Bk.length) 1))).max? = some P.length
    rw [hL1]
    refine List.max?_eq_some_iff.mpr ⟨?_, ?_⟩
    · exact List.mem_filter.mpr ⟨hchain _ (by omega) (Nat.le_refl _),
        decide_eq_true (by rw [hP1]; exact hvw)⟩
    · intro z hz
      obtain ⟨hz1, hz2⟩ := List.mem_filter.mp hz
      rcases Nat.lt_or_ge P.length z with h | h
      · exfalso
        have hzL : z < P.length + Bk.length :=
          iterParent_lt (fun x y hy => parent_lt _ 0 x y hy) _ _ z hz1
        have hlm := (mem_iterParent0 _ (P.length + Bk.length) (P.length + Bk.length) z
          (Nat.le_refl _)).mp hz1
        have h1 := hanc z h hzL hlm
        have h2 := of_decide_eq_true hz2
        omega
      · exact h
  rw [expand?_lim _ [d + e, w] 1 P.length
      (frame_getLast P Bk [d + e, w]) (by rw [lnz_pair, if_pos (by omega)])
      (by rw [hlen]; simpa using hp1) n]
  rw [take_left_len]
  refine congrArg some (congrArg (P ++ ·) ?_)
  have hblock : ∀ (m : Nat),
      (List.range ((P ++ (Bk ++ [[d + e, w]])).length - 1 - P.length)).map (fun x =>
        (List.range ([d + e, w] : Col).length).map fun y =>
          ent (P ++ (Bk ++ [[d + e, w]])) (P.length + x) y
            + m * delta (P ++ (Bk ++ [[d + e, w]])) P.length 1 y
              * (if ascends (P ++ (Bk ++ [[d + e, w]])) P.length (P.length + x) y then 1 else 0))
      = sh (m * e) Bk := by
    intro m
    rw [show (P ++ (Bk ++ [[d + e, w]])).length - 1 - P.length = Bk.length from by
      rw [hlen]; omega]
    show _ = Bk.map (shc (m * e))
    refine Eq.trans (List.map_congr_left ?_) (map_getD_range_map [] (shc (m * e)) Bk)
    intro x hx
    rw [List.mem_range] at hx
    rw [show (List.range ([d + e, w] : Col).length) = [0, 1] from rfl]
    have hd0 : delta (P ++ (Bk ++ [[d + e, w]])) P.length 1 0 = e := by
      show (if 0 < 1 then ent (P ++ (Bk ++ [[d + e, w]]))
        ((P ++ (Bk ++ [[d + e, w]])).length - 1) 0 - _ else 0) = e
      rw [if_pos (by omega), show (P ++ (Bk ++ [[d + e, w]])).length - 1
        = P.length + Bk.length from by rw [hlen]; omega, hL0, hP0]
      omega
    have hd1 : delta (P ++ (Bk ++ [[d + e, w]])) P.length 1 1 = 0 := by
      show (if 1 < 1 then _ else 0) = 0
      rw [if_neg (by omega)]
    have hasc : ascends (P ++ (Bk ++ [[d + e, w]])) P.length (P.length + x) 0 = true := by
      match x, hx with
      | 0, _ => show ((P.length + 0 == P.length) || _) = true
                simp
      | j + 1, hx =>
        show ((P.length + (j + 1) == P.length) || _) = true
        rw [show (iterParent (parent (P ++ (Bk ++ [[d + e, w]])) 0)
            (P.length + (j + 1)) (P.length + (j + 1))).contains P.length = true from by
          have := hchain (P.length + (j + 1)) (by omega) (by omega)
          simpa using this]
        exact Bool.or_true _
    have hent : ∀ y, ent (P ++ (Bk ++ [[d + e, w]])) (P.length + x) y
        = (Bk.getD x []).getD y 0 := by
      intro y; rw [frame_ent P Bk [d + e, w] x y hx]; rfl
    simp only [List.map_cons, List.map_nil, hd0, hd1, hasc, hent,
      Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_one, if_true]
    rw [shc_len2 (m * e) (Bk.getD x []) (hlen2 _ (getD_mem Bk [] x hx))]
  rw [List.map_congr_left (fun m _ => hblock m)]

/-! ## §12 THE FAR CASE

§11 instantiated at the region's own block.  `hanc` is §9 transported across the two
appends, and the conclusion is `iterD` — the context iteration §3.2 measured. -/

theorem expand_far (v : Nat) (a : B) (ha : a ≠ .nil)
    (hvw : v < lastLvl a) (hlow : hasLowAnc (lastLvl a) a = false)
    (P : Matrix) (d n : Nat) :
    expand? (P ++ matB (.nd v .nil a) d) n = some (P ++ matB (iterD v a n) d) := by
  have hMs : matB (.nd v .nil a) d
      = matB (.nd v .nil (plugB a .nil)) d ++ [[d + (lastDep a + 1), lastLvl a]] := by
    rw [matB_split v a ha d, show d + (lastDep a + 1) = d + 1 + lastDep a from by omega]
  have hBkLen : (matB (.nd v .nil (plugB a .nil)) d).length = (matB a (d + 1)).length := by
    rw [matB_bad v a ha d]
    show ((matB a (d + 1)).dropLast).length + 1 = _
    rw [List.length_dropLast]
    have := matB_len_pos a (d + 1) ha
    omega
  have hM2 : P ++ (matB (.nd v .nil (plugB a .nil)) d
        ++ [[d + (lastDep a + 1), lastLvl a]])
      = (P ++ [[d, v]]) ++ matB a (d + 1) := by
    rw [← hMs]
    show P ++ ([d, v] :: matB a (d + 1)) = _
    rw [List.append_assoc]
    rfl
  have hpre : (P ++ [[d, v]]).length = P.length + 1 := by rw [List.length_append]; simp
  have hentTr : ∀ i y, ent (P ++ (matB (.nd v .nil (plugB a .nil)) d
        ++ [[d + (lastDep a + 1), lastLvl a]])) (P.length + 1 + i) y
      = ent (matB a (d + 1)) i y := by
    intro i y
    rw [hM2, ent_append (P ++ [[d, v]]) _ _ y (by rw [hpre]; omega), hpre,
      show P.length + 1 + i - (P.length + 1) = i from by omega]
  have hanc : ∀ q, P.length < q →
      q < P.length + (matB (.nd v .nil (plugB a .nil)) d).length →
      LMin (P ++ (matB (.nd v .nil (plugB a .nil)) d
        ++ [[d + (lastDep a + 1), lastLvl a]])) q
        (P.length + (matB (.nd v .nil (plugB a .nil)) d).length) →
      lastLvl a ≤ ent (P ++ (matB (.nd v .nil (plugB a .nil)) d
        ++ [[d + (lastDep a + 1), lastLvl a]])) q 1 := by
    intro q h1 h2 hlm
    obtain ⟨_, hlm2⟩ := hlm
    have hq : q = P.length + 1 + (q - P.length - 1) := by omega
    have hi : q - P.length - 1 < (matB a (d + 1)).length - 1 := by rw [hBkLen] at h2; omega
    have key := anc_lvl a ha hlow (d + 1) (q - P.length - 1) hi (by
      intro p hp1 hp2
      have hp : P.length + 1 + p ≤ P.length + (matB (.nd v .nil (plugB a .nil)) d).length := by
        rw [hBkLen]; omega
      have hh := hlm2 (P.length + 1 + p) (by omega) hp
      rw [hq, hentTr (q - P.length - 1) 0, hentTr p 0] at hh
      exact hh)
    rw [hq, hentTr (q - P.length - 1) 1]
    exact key
  rw [hMs, expand_frame_gap P (matB (.nd v .nil (plugB a .nil)) d) d v (lastLvl a)
      (lastDep a + 1) (ent_blkB_root v (plugB a .nil) d) (ent_blkB_root1 v (plugB a .nil) d)
      hvw (by omega) (blkB_in v (plugB a .nil) d) (blkB_len2 v (plugB a .nil) d)
      (blkB_pos v (plugB a .nil) d) hanc n,
    flatten_iterD_gen v a ha d n]

/-! ## §13 THE EXPANSION IDENTITY, UNCONDITIONAL

The recursion now has no hole.  At a `ψ_v` node with argument `a ≠ 0` there are three cases
and `resB` says which:

    lastLvl a = 0                      the last node is `ψ₀(0)` — repeat the parent (§5)
    hasLowAnc (lastLvl a) a = true     a lower-level ancestor is DEEPER — descend (§5)
    v < lastLvl a                      this node IS the bad root — §12's far case

and `resB` propagates into the descent because `hasLowAnc w (nd u b c) = (u < w) ∨
hasLowAnc w c` is the same disjunction the inner call needs.  At the TOP the node's level is
`0`, so the third case holds whenever the first two fail — which is why `expand_matB` needs
no hypothesis beyond `topOKB`.

**`Hclosed` for the generalised region.**  This is `Region.expand_mat` one constructor
wider, and it is what `certIn_region` asks for first. -/

/-- 悪い根がこのブロックの中か、この節自身であること。 -/
def resB (v : Nat) (a : B) : Bool :=
  (lastLvl a == 0) || hasLowAnc (lastLvl a) a || decide (v < lastLvl a)

theorem expand_blkB : ∀ (a : B), a ≠ .nil → ∀ (v : Nat), resB v a = true →
    ∀ (P : Matrix) (d n : Nat),
      expand? (P ++ matB (.nd v .nil a) d) n = some (P ++ matB (stepBv v .nil a n) d) := by
  intro a
  induction a with
  | nil => intro h; exact absurd rfl h
  | nd u b c _ ihc =>
    intro _ v hres P d n
    cases c with
    | nil =>
      cases u with
      | zero =>
        rw [expand_prinB_succ v b P d n]
        refine congrArg some (congrArg (P ++ ·) (congrArg (matB · d) ?_))
        show _ = if lastLvl (B.nd 0 b .nil) == 0 then repB (.nd v .nil (.nd 0 b .nil)) n else _
        rw [if_pos (show (lastLvl (B.nd 0 b (B.nil)) == 0) = true from rfl)]
        show _ = appB .nil (repNode v b n)
        rw [appB_nil]
      | succ k =>
        have hlow : hasLowAnc (lastLvl (B.nd (k + 1) b .nil)) (.nd (k + 1) b .nil) = false := rfl
        have hvw : v < lastLvl (B.nd (k + 1) b .nil) := by
          have hb : ((lastLvl (B.nd (k+1) b .nil) == 0)
            || hasLowAnc (lastLvl (B.nd (k+1) b .nil)) (.nd (k+1) b .nil)
            || decide (v < lastLvl (B.nd (k+1) b .nil))) = true := hres
          rw [show (lastLvl (B.nd (k+1) b (B.nil)) == 0) = false from rfl, hlow] at hb
          simp at hb
          exact hb
        rw [expand_far v (.nd (k + 1) b .nil) (by intro h; exact B.noConfusion h) hvw hlow P d n]
        refine congrArg some (congrArg (P ++ ·) (congrArg (matB · d) ?_))
        show _ = if lastLvl (B.nd (k+1) b .nil) == 0 then _
                 else rwB (lastLvl (B.nd (k+1) b .nil)) n (.nd v .nil (.nd (k+1) b .nil))
        rw [if_neg (show ¬((lastLvl (B.nd (k+1) b (B.nil)) == 0) = true) from by simp [lastLvl])]
        show _ = (if hasLowAnc (k+1) (.nd (k+1) b .nil) then _
                  else if v < k + 1 then appB .nil (iterD v (.nd (k+1) b .nil) n) else _)
        rw [if_neg (show ¬(hasLowAnc (k+1) (B.nd (k+1) b (B.nil)) = true) from by simp [hasLowAnc]),
          if_pos (show v < k + 1 from hvw), appB_nil]
    | nd u' b' c' =>
      by_cases hdeep : ((lastLvl (B.nd u' b' c') == 0)
          || hasLowAnc (lastLvl (B.nd u' b' c')) (.nd u b (.nd u' b' c'))) = true
      · -- 悪い根はもっと深い: 1 段落ちる
        have h' : resB u (.nd u' b' c') = true := by
          show ((lastLvl (B.nd u' b' c') == 0)
            || hasLowAnc (lastLvl (B.nd u' b' c')) (.nd u' b' c')
            || decide (u < lastLvl (B.nd u' b' c'))) = true
          have : ((lastLvl (B.nd u' b' c') == 0)
            || (decide (u < lastLvl (B.nd u' b' c'))
                || hasLowAnc (lastLvl (B.nd u' b' c')) (.nd u' b' c'))) = true := hdeep
          revert this
          cases (lastLvl (B.nd u' b' c') == 0) <;>
            cases (decide (u < lastLvl (B.nd u' b' c'))) <;>
            cases (hasLowAnc (lastLvl (B.nd u' b' c')) (B.nd u' b' c')) <;> simp
        have hstep := ihc (by intro h; exact B.noConfusion h) u h'
        rw [expand_prinB_deep v u b (.nd u' b' c') (stepBv u .nil (.nd u' b' c') n) n
          (fun P' d' => hstep P' d' n) P d]
        refine congrArg some (congrArg (P ++ ·) (congrArg (matB · d) ?_))
        show B.nd v .nil (appB b (stepBv u .nil (.nd u' b' c') n))
          = if lastLvl (B.nd u b (.nd u' b' c')) == 0 then
              repB (.nd v .nil (.nd u b (.nd u' b' c'))) n
            else rwB (lastLvl (B.nd u b (.nd u' b' c'))) n (.nd v .nil (.nd u b (.nd u' b' c')))
        rw [← stepBv_prefix u b u' b' c' n]
        by_cases h0 : (lastLvl (B.nd u b (.nd u' b' c')) == 0) = true
        · rw [if_pos h0,
            show repB (B.nd v .nil (.nd u b (.nd u' b' c'))) n
              = B.nd v .nil (repB (.nd u b (.nd u' b' c')) n) from by cases u <;> rfl]
          refine congrArg (B.nd v .nil) ?_
          show (if lastLvl (B.nd u' b' c') == 0 then repB (.nd u b (.nd u' b' c')) n else _) = _
          rw [if_pos (show (lastLvl (B.nd u' b' c') == 0) = true from h0)]
        · rw [if_neg h0]
          have hla : hasLowAnc (lastLvl (B.nd u b (.nd u' b' c'))) (.nd u b (.nd u' b' c'))
              = true := by
            have : ((lastLvl (B.nd u' b' c') == 0)
              || hasLowAnc (lastLvl (B.nd u' b' c')) (.nd u b (.nd u' b' c'))) = true := hdeep
            rw [show (lastLvl (B.nd u' b' c') == 0) = false from by
              cases hz : (lastLvl (B.nd u' b' c') == 0) with
              | false => rfl
              | true => exact absurd (show (lastLvl (B.nd u b (.nd u' b' c')) == 0) = true from hz) h0]
              at this
            simpa using this
          rw [show rwB (lastLvl (B.nd u b (.nd u' b' c'))) n
                (B.nd v .nil (.nd u b (.nd u' b' c')))
              = B.nd v .nil (rwB (lastLvl (B.nd u b (.nd u' b' c'))) n
                  (.nd u b (.nd u' b' c'))) from by
            show (if hasLowAnc (lastLvl (B.nd u b (.nd u' b' c'))) (.nd u b (.nd u' b' c')) then
                    B.nd v .nil (rwB (lastLvl (B.nd u b (.nd u' b' c'))) n
                      (.nd u b (.nd u' b' c')))
                  else _) = _
            rw [if_pos hla]]
          refine congrArg (B.nd v .nil) ?_
          show (if lastLvl (B.nd u' b' c') == 0 then _
                else rwB (lastLvl (B.nd u' b' c')) n (.nd u b (.nd u' b' c'))) = _
          rw [if_neg (show ¬((lastLvl (B.nd u' b' c') == 0) = true) from h0)]
          rfl
      · -- 悪い根はこの節: 差が `e` の骨組み
        have hz : (lastLvl (B.nd u b (.nd u' b' c')) == 0) = false := by
          cases hzz : (lastLvl (B.nd u' b' c') == 0) with
          | false => exact hzz
          | true => exact absurd (by rw [show (lastLvl (B.nd u' b' c') == 0) = true from hzz]; rfl) hdeep
        have hlow : hasLowAnc (lastLvl (B.nd u b (.nd u' b' c'))) (.nd u b (.nd u' b' c'))
            = false := by
          cases hh : hasLowAnc (lastLvl (B.nd u b (.nd u' b' c'))) (B.nd u b (.nd u' b' c')) with
          | false => rfl
          | true =>
            exact absurd (show ((lastLvl (B.nd u' b' c') == 0)
              || hasLowAnc (lastLvl (B.nd u' b' c')) (.nd u b (.nd u' b' c'))) = true from by
              rw [show hasLowAnc (lastLvl (B.nd u' b' c')) (B.nd u b (.nd u' b' c')) = true
                from hh]
              exact Bool.or_true _) hdeep
        have hvw : v < lastLvl (B.nd u b (.nd u' b' c')) := by
          have hb : ((lastLvl (B.nd u b (.nd u' b' c')) == 0)
            || hasLowAnc (lastLvl (B.nd u b (.nd u' b' c'))) (.nd u b (.nd u' b' c'))
            || decide (v < lastLvl (B.nd u b (.nd u' b' c')))) = true := hres
          rw [hz, hlow] at hb
          simp at hb
          exact hb
        rw [expand_far v (.nd u b (.nd u' b' c')) (by intro h; exact B.noConfusion h)
          hvw hlow P d n]
        refine congrArg some (congrArg (P ++ ·) (congrArg (matB · d) ?_))
        show _ = if lastLvl (B.nd u b (.nd u' b' c')) == 0 then _
                 else rwB (lastLvl (B.nd u b (.nd u' b' c'))) n
                        (.nd v .nil (.nd u b (.nd u' b' c')))
        rw [if_neg (show ¬((lastLvl (B.nd u b (.nd u' b' c')) == 0) = true) from by
            rw [hz]; exact Bool.noConfusion)]
        show _ = (if hasLowAnc (lastLvl (B.nd u b (.nd u' b' c'))) (.nd u b (.nd u' b' c')) then _
                  else if v < lastLvl (B.nd u b (.nd u' b' c')) then
                    appB .nil (iterD v (.nd u b (.nd u' b' c')) n) else _)
        rw [if_neg (show ¬(hasLowAnc (lastLvl (B.nd u b (.nd u' b' c')))
            (B.nd u b (.nd u' b' c')) = true) from by rw [hlow]; exact Bool.noConfusion),
          if_pos hvw, appB_nil]

/-- **一般化した領域は展開で閉じている。** 仮定は最上位の加数が `ψ₀` であることだけ。 -/
theorem expand_matB : ∀ (t : B), topOKB t = true → t ≠ .nil → ∀ (n : Nat),
    expand? (matB t 0) n = some (matB (fsB t n) 0) := by
  intro t
  cases t with
  | nil => intro _ h; exact absurd rfl h
  | nd v r a =>
    cases a with
    | nil =>
      intro htop _ n
      have hv : v = 0 := by
        have hb : ((v == 0) && topOKB r) = true := htop
        simp at hb
        exact hb.1
      subst hv
      show expand? (matB r 0 ++ [[0, 0]]) n = some (matB (fsB (.nd 0 r .nil) n) 0)
      rw [expand?_succ _ [0, 0] (by simp) (by rw [lnz_pair]; simp) n]
      show some (matB r 0 ++ [[0, 0]]).dropLast = some (matB r 0)
      simp
    | nd w b c =>
      intro htop _ n
      have hv : v = 0 := by
        have hb : ((v == 0) && topOKB r) = true := htop
        simp at hb
        exact hb.1
      subst hv
      have hres : resB 0 (.nd w b c) = true := by
        show ((lastLvl (B.nd w b c) == 0) || hasLowAnc (lastLvl (B.nd w b c)) (.nd w b c)
          || decide (0 < lastLvl (B.nd w b c))) = true
        cases hz : (lastLvl (B.nd w b c) == 0) with
        | true => rfl
        | false =>
          have : 0 < lastLvl (B.nd w b c) := by
            cases hl : lastLvl (B.nd w b c) with
            | zero => rw [hl] at hz; exact absurd hz (by simp)
            | succ _ => omega
          rw [show decide (0 < lastLvl (B.nd w b c)) = true from by simp; omega]
          exact Bool.or_true _
      show expand? (matB r 0 ++ matB (.nd 0 .nil (.nd w b c)) 0) n = _
      rw [expand_blkB (.nd w b c) (by intro h; exact B.noConfusion h) 0 hres (matB r 0) 0 n,
        ← matB_app (stepBv 0 .nil (.nd w b c) n) r 0,
        ← stepBv_prefix 0 r w b c n, ← fsB_eq_stepBv 0 r w b c n]

/-! ### §13.1 THE HYPOTHESIS IS NOT A RESTRICTION

`topOKB` says the top-level summands are `ψ₀` nodes — the value is below `Ω`.  Every row of
the table and every matrix of §3.5's population satisfies it, so `expand_matB` covers the
whole population, not a fragment of it. -/

#guard wideRows.all fun M => match decodeB M with | none => true | some t => topOKB t
#guard popB.all fun S => match decodeB S with | none => true | some t => topOKB t

/-! ## §14 THE VALUE, MEASURED — and why `RegionV`'s route does not generalise

`Hclosed` is done (§13).  The other three supplies need a VALUE, and `Evidence/RegionV.lean`
gets one for the current region out of two pieces: `argVal`, which reads a run of `Ω`s as
`ε`, and `omegaNF`, Rathjen's `ω^·`.  Does that generalise?  Measured on the 848 indices that
occur in the depth-two closure of the table's 52 width-two rows and all their subtrees
(`Trans.oR` is candidate tier and appears in no justification — this is a measurement):

    848 / 848   `oR` is defined on every index, so the region's value is total
    all true    THE PREFIX SPLITS OFF:  val (nd v r a) = val r ⊕ val (nd v .nil a)

so the value is a SUM over the top-level summands, exactly as `sumVal` is.  The node
function is where it stops being like `RegionV`.  Write `Ω_k` for `Z k` and `Ω_{-1}` for `0`:

    val (nd v .nil a) = ω^(Ω_{v-1} ⊕ val a)      **iff**   val a < Ω_{v+1}

and the `iff` is exact — `powFits v x y == belowOm v y` holds at every one of the 519 nodes.
The four-way split says how much of the region that leaves:

    v = 0, arg ≥ Ω        344      a collapse
    v ≥ 1, arg ≥ Ω_{v+1}   87      a collapse
    v ≥ 1, arg < Ω_{v+1}   83      an ω-power
    v = 0, arg < Ω          5      an ω-power

**431 of 519 nodes are genuine collapses.**  `ψ_v` only looks like `ω^(Ω_{v-1} ⊕ ·)` while its
argument stays below `Ω_{v+1}`; at `Ω_{v+1}` it collapses, and the first one is
`ψ₁(Ω₂) = φ̄(1,Ω) = ε_Ω`.  `RegionV`'s `argVal`-then-`omegaNF` is the case `v = 0` with the
argument a run of `Ω`s, which is 5 of the 519 plus the `Ω`-tower dressing — so the route does
NOT generalise, and the value side of this region needs Rathjen's `ψ` rather than a second
reading of `ω^·`.

That is a statement about the DESIGN, not a refutation of anything: `oR` computes the right
value everywhere here.  What it fixes is that the next piece of work is a collapsing function
on `𝔗(M)` terms, and its correctness — not a valuation built out of `ω^·`. -/

section
open TM TM.Term

/-- 添字の値 (測定用)。`Trans.oR` は候補段であり、根拠には使わない。 -/
def valT (t : B) : Option Term := Trans.oR (matB t 0)

partial def subsB : B → List B
  | .nil => [.nil]
  | .nd v r a => (B.nd v r a) :: (subsB r ++ subsB a)

/-- 母集団: 幅 2 の 52 行の深さ 2 の閉包に現れる添字と、そのすべての部分木。 -/
def valCorpus : List B :=
  ((wideRows.flatMap fun M => cloOf M 3 2).eraseDups.filterMap decodeB).flatMap subsB
    |>.eraseDups

def OmT (k : Nat) : Term := Z (ofNat k)
def belowOm (v : Nat) (y : Term) : Bool := lt y (OmT v)
def powFits (v : Nat) (x y : Term) : Bool :=
  if v == 0 then x == omegaNF y else x == omegaNF (plus (OmT (v - 1)) y)

#guard valCorpus.length == 848
#guard valCorpus.all fun t => (valT t).isSome
-- 前置きは外に出る。
#guard valCorpus.all fun t => match t with
  | .nil => true
  | .nd v r a =>
    match valT (.nd v r a), valT r, valT (.nd v .nil a) with
    | some x, some y, some z => x == plus y z
    | _, _, _ => false
-- `ω` 冪の形になるのは引数が `Ω_{v+1}` 未満のとき**ちょうど**。
#guard valCorpus.all fun t => match t with
  | .nd v .nil a =>
    match valT (.nd v .nil a), valT a with
    | some x, some y => powFits v x y == belowOm v y
    | _, _ => false
  | _ => true
-- 4 分割。**431 / 519 は本物の collapse。**
#guard (valCorpus.filter fun t => match t with
  | .nd 0 .nil a => match valT a with | some y => !(belowOm 0 y) | none => false
  | _ => false).length == 344
#guard (valCorpus.filter fun t => match t with
  | .nd v .nil a => v ≥ 1 && (match valT a with | some y => !(belowOm v y) | none => false)
  | _ => false).length == 87
#guard (valCorpus.filter fun t => match t with
  | .nd v .nil a => v ≥ 1 && (match valT a with | some y => belowOm v y | none => false)
  | _ => false).length == 83
#guard (valCorpus.filter fun t => match t with
  | .nd 0 .nil a => match valT a with | some y => belowOm 0 y | none => false
  | _ => false).length == 5
-- 最初の collapse。
#guard (match valT (.nd 1 .nil (.nd 2 .nil .nil)) with
  | some x => x == phi one (Z zero)
  | none => false)

end

/-! ## §15 `B` IS A COORDINATE SYSTEM FOR MATRICES, NOT A BUCHHOLZ ENCODING

§14 says the value side needs a collapsing function on `𝔗(M)` terms, and the repository
already HAS one: `Trans/Dict.lean`'s `dict`, which is compositional —
`dict (D u a) = collapse u (dict a)`, `dict (sum a b) = dict a ⊕ dict b`.  So the obvious
shortcut is to read a `B` index as a Buchholz term (`nd v r a` ↦ `r ⊕ ψ_v(a)`) and take
`dict` of it.  **The shortcut is wrong, and this section pins where.**

    oRB (0,0)(1,1)(2,2)   =  ψ₀(ψ₂(0))          the BMS → Buchholz map
    encB of the same      =  ψ₀(ψ₁(ψ₂(0)))      reading the row-1 entry as the subscript

and `dict` separates them.  `Trans/Dict.lean` §4 records that THREE independent things put
that matrix at `ψ₀(ψ₂(0))` — this repository's own port of naruyoko's pss2bp (`oRB`),
Hexirp's published analysis, and the BMS-vs-Rathjen spreadsheet — so it is `encB` that is
out, not `oRB`.  MEASURED over §14's 848 indices:

    618 / 848    `dict (encB t)` agrees with `oR (matB t 0)`
      1          matrix of ≤ 3 columns where they differ, and it is `(0,0)(1,1)(2,2)`

WHAT THIS DOES AND DOES NOT TOUCH.  `B` was never claimed to be a Buchholz encoding.  §2
claims `matB (decodeB M) 0 = M` — a faithful coordinate system for MATRICES — and §13's
`expand_matB` is an identity between matrices.  Both stand: `decodeB` reads a width-two
matrix as a forest by its row-0 entries, which is exactly what `BMS.expand` acts on, and the
row-1 entry is a LABEL there, not a `ψ` subscript.  What falls is only the shortcut for the
VALUE.

So the value side still needs its own function, and §14's measurement is what pins it down:
the prefix splits off, and the node function is `ω^(Ω_{v-1} ⊕ ·)` exactly below `Ω_{v+1}`.
Above that it collapses, and the collapse is NOT `dict ∘ encB`. -/

section
open TM TM.Term

/-- 添字を素直に Buchholz 項として読んだもの。**これは BMS → Buchholz の写像ではない。** -/
def encB : B → Trans.Dict.BT
  | .nil => .zero
  | .nd v .nil a => .D v (encB a)
  | .nd v r a => .sum (encB r) (.D v (encB a))

-- 出典側の読み (`Trans/Dict.lean` §4)。
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2]] == some (.D 0 (.D 2 .zero))
-- `B` の読み。
#guard encB (.nd 0 .nil (.nd 1 .nil (.nd 2 .nil .nil)))
  == Trans.Dict.BT.D 0 (.D 1 (.D 2 .zero))
-- 値は違う。
#guard Trans.Dict.dict (.D 0 (.D 2 .zero))
  != Trans.Dict.dict (.D 0 (.D 1 (.D 2 .zero)))
-- 母集団での一致数と、3 列以下で食い違う唯一の行列。
#guard (valCorpus.filter fun t =>
  match Trans.oR (matB t 0) with
  | none => false
  | some u => u == Trans.Dict.dict (encB t)).length == 618
#guard (valCorpus.filter fun t => (matB t 0).length ≤ 3 &&
  (match Trans.oR (matB t 0) with
   | none => true
   | some u => u != Trans.Dict.dict (encB t))).map (fun t => matB t 0)
  == [[[0,0], [1,1], [2,2]]]

end

/-! ## §16 THE NODE FUNCTION IS NEITHER OF THE TWO CANDIDATES

§14 says the value is compositional in `B`'s coordinates — the prefix splits off and the
node function `f v x` exists — and §15 says the index cannot simply be read as a Buchholz
term.  Two candidates for `f` remain, and both are now excluded with numbers.

**(a) `ω^(Ω_{v-1} ⊕ ·)`.**  §14 already settles it: that IS `f` below `Ω_{v+1}` and never
above, so it covers 88 of the 519 nodes and the other 431 are collapses.

**(b) `Trans/Dict.lean`'s `collapse v`.**  This is the repository's own Buchholz-to-`𝔗(M)`
collapsing, and it does much better — 398 of 519, INCLUDING all 88 where (a) works.  But it
is not `f` either, and its smallest failure is the same matrix §15 found:

    (0,0)(1,1)(2,2)     f          ψ_Ω(Ω₂)
                        collapse   ψ_Ω(ε_Ω)

— the only matrix of three columns or fewer where they differ.  Composing `collapse` down
the whole index reproduces `dict ∘ encB` exactly, 618 of 848, as it must.

SO BOTH FAILURES ARE THE SAME FAILURE.  `transPort` — the BMS → Buchholz map — is not a tree
read at all: it is naruyoko's `Trans`/`Mark` recursion with seven case types, marks and
memoisation (`Trans/Recal.lean` §3), and at `(0,0)(1,1)(2,2)` it takes the branch that builds
`ψ₀(ψ_v(0))` out of the LAST column's row-1 entry alone.  No per-node function of `B` can
imitate that by looking only at `(v, value of the argument)` — except that, measured, one
does on this corpus (§14's 847 keys with no conflict).  What is missing is a closed form for
it, and the two obvious ones are gone.

That is where the value side stands: specified (§14), with the shortcut (§15) and both
candidates (§16) excluded.  `Hclosed` (§13) does not depend on any of it. -/

section
open TM TM.Term

/-- 節だけを集めたもの (前置きなし)。 -/
def nodeCorpus : List B :=
  valCorpus.filter fun t => match t with | .nd _ .nil _ => true | _ => false

/-- 候補 (b): 節の関数は `Dict.collapse` か。 -/
def okCollapse (t : B) : Bool :=
  match t with
  | .nd v .nil a =>
    match Trans.oR (matB t 0), Trans.oR (matB a 0) with
    | some x, some y => x == Trans.Dict.collapse v y
    | _, _ => false
  | _ => false

#guard nodeCorpus.length == 519
#guard (nodeCorpus.filter okCollapse).length == 398
-- (a) が当たる 88 個は (b) も当てる。
#guard ((nodeCorpus.filter fun t => match t with
  | .nd v .nil a => match Trans.oR (matB a 0) with | some y => belowOm v y | none => false
  | _ => false).filter okCollapse).length == 88
-- (b) が外す 3 列以下の節は 1 つだけで、§15 と同じ行列。
#guard (nodeCorpus.filter fun t =>
  !(okCollapse t) && (matB t 0).length ≤ 3).map (fun t => matB t 0)
  == [[[0,0], [1,1], [2,2]]]

end

/-! ## §17 THE ARGUMENT NEEDS ITS OWN VALUATION — and the reading rule, measured

§16 excluded `Dict.collapse v` as the node function.  That exclusion was measured against
the WRONG input.  `Evidence/RegionV.lean` already makes the distinction the measurement
missed: `sumVal` is the value of an index read as a TOP-LEVEL sum, `argVal` the value of the
same index read as an ARGUMENT, and they differ (there, by reading a run of `Ω`s as `ε`).
§14–§16 fed `collapse` the sum valuation.

With the argument valuation instead — take `oRB` of `ψ₀(a)`'s matrix and strip the outer
`ψ₀` — the recursion

    sumV (nd v r a)  =  sumV r ⊕ collapse v (argV a)

holds at **696 of 847** nodes, against 618 for the sum valuation.  And the two disagree
exactly where one would expect:

    y2(0)        argV  Ω        sumV  Ω₂
    y1(y2(0))    argV  Ω₂       sumV  ε_Ω

THE READING RULE (measured on a designed family, `#guard`s below).  Along a chain of nodes
with levels `v₁, v₂, …` under the top `ψ₀`:

    drop a node whose level is STRICTLY BELOW the next node's level;
    a kept node's subscript is the RANK of its level among the distinct levels
    seen along the chain up to it (the top counting as rank 0).

    (0,0)(1,2)              ψ₀(ψ₁(0))         levels {0,2}: rank of 2 is 1
    (0,0)(1,1)(2,2)         ψ₀(ψ₂(0))         1 < 2 so the ψ₁ node goes; rank of 2 is 2
    (0,0)(1,1)(2,2)(3,3)    ψ₀(ψ₃(0))         two nodes go
    (0,0)(1,1)(2,2)(3,1)    ψ₀(ψ₂(ψ₁(0)))     the last node is kept, at rank 1
    (0,0)(1,2)(2,2)         ψ₀(ψ₁(ψ₁(0)))     2 is not < 2, so both are kept, both rank 1

That is why §15's `encB` — which reads the row-1 entry AS the subscript and keeps every node
— disagrees, and why the disagreement starts at `(0,0)(1,1)(2,2)`: it is the smallest matrix
with a strictly increasing pair of levels on the chain.

WHAT IS STILL OPEN.  The rule above is for CHAINS.  Sums inside an argument are not covered
by it — `(0,0)(1,1)(2,2)(2,1)` reads as `ψ₀(ψ₂(0) ⊕ ψ₁(ψ₂(0) ⊕ ψ₁(0)))`, which the chain
rule does not produce — and that is exactly the 151 of 847 the recursion above still misses.
So the next step is the rule for sums, not another candidate for the node function. -/

section
open TM TM.Term

/-- 引数として読んだときの Buchholz 項 (測定用): `ψ₀(a)` の行列を訳して外側を剥がす。 -/
def argBT (a : B) : Option Trans.Dict.BT :=
  match Trans.Recal.oRB (matB (.nd 0 .nil a) 0) with
  | some (.D 0 u) => some u
  | _ => none

def argV (a : B) : Option Term := (argBT a).map Trans.Dict.dict
def sumV (t : B) : Option Term := Trans.oR (matB t 0)

-- `argBT` は `nil` 以外で定義される (`ψ₀(0)` の行列は `(0)` で、`oRB` は `0` を返す)。
#guard (valCorpus.filter fun a => (argBT a).isSome).length == 847
#guard (valCorpus.filter fun a => (argBT a).isNone) == [B.nil]
-- 引数の値付けで再帰は 696 / 847。
#guard (valCorpus.filter fun t => match t with
  | .nil => false
  | .nd v r a =>
    match sumV (.nd v r a), sumV r, argV a with
    | some x, some y, some z => x == plus y (Trans.Dict.collapse v z)
    | _, _, _ => false).length == 696
#guard (valCorpus.filter fun t => match t with | .nil => false | _ => true).length == 847
-- 引数の値付けは和の値付けと違う。
#guard argV (.nd 2 .nil .nil) == some (Z zero)
#guard sumV (.nd 2 .nil .nil) == some (Z one)
#guard argV (.nd 1 .nil (.nd 2 .nil .nil)) == some (Z one)
#guard sumV (.nd 1 .nil (.nd 2 .nil .nil)) == some (phi one (Z zero))

/-! ### §17.1 THE READING RULE ON A CHAIN -/

#guard Trans.Recal.oRB [[0,0], [1,2]] == some (.D 0 (.D 1 .zero))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,1]] == some (.D 0 (.D 1 (.D 1 .zero)))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2]] == some (.D 0 (.D 2 .zero))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2], [3,3]] == some (.D 0 (.D 3 .zero))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2], [3,1]] == some (.D 0 (.D 2 (.D 1 .zero)))
#guard Trans.Recal.oRB [[0,0], [1,2], [2,2]] == some (.D 0 (.D 1 (.D 1 .zero)))
-- 和は鎖の規則では出ない。
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2], [2,1]]
  == some (.D 0 (.sum (.D 2 .zero) (.D 1 (.sum (.D 2 .zero) (.D 1 .zero)))))

end

/-! ### §17.2 SUMS INSIDE AN ARGUMENT — the family, measured

The chain rule of §17.1 does not reach sums.  Here is what a designed family shows.  Write
`y v (·)` for a `B` node of level `v`; the reading is `oRB`.

    B                          oRB
    y0(y1(0)+y1(0))            y0(y1(0)+y1(0))                 unchanged
    y0(y1(y1(0)+y1(0)))        y0(y1(y1(0)+y1(0)))             unchanged
    y0(y1(y2(0)+y2(0)))        y0(y2(0)+y2(0))                 the node VANISHES
    y0(y1(y2(0)+y1(0)))        y0(y2(0)+y1(y2(0)+y1(0)))       HOISTED, and copied inside
    y0(y1(y2(0)+y1(0)+y1(0)))  y0(y2(0)+y1(y2(0)+y1(0)+y1(0))) same
    y0(y1(y2(y1(0))+y1(0)))    y0(y2(y1(0))+y1(y2(y1(0))+y1(0)))
    y0(y1(y2(y3(0))+y1(0)))    y0(y3(0)+y1(y3(0)+y1(0)))       §17.1 inside, then hoisting
    y0(y1(y2(y1(0)+y1(0))))    y0(y2(y1(0)+y1(0)))             the node VANISHES
    y0(y1(y2(0))+y1(0))        y0(y2(0)+y1(0))                 per summand, no hoisting out

WHAT IS CONFIRMED.  §17.1's drop is the case where the node's argument has NO summand of its
own level or below: then the node vanishes and its whole argument takes its place.  When the
argument's last summand is at the node's level or below, the node survives, and any summands
ABOVE its level are copied out in front of it — while ALSO staying inside.  That copy is what
no per-node function can produce, and it is why §16's `collapse` misses those nodes.

WHAT IS NOT SETTLED.  The top `ψ₀` never hoists (last line), though its summands are all
above its level; so the rule is not simply "hoist what is above me".  Until that is pinned,
the sum rule is a description of this family and nothing more.  It is recorded because the
copy phenomenon is the thing to design against, not because it is the rule. -/

section
open TM TM.Term

#guard Trans.Recal.oRB [[0,0], [1,1], [2,1], [2,1]]
  == some (.D 0 (.D 1 (.sum (.D 1 .zero) (.D 1 .zero))))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2], [2,2]]
  == some (.D 0 (.sum (.D 2 .zero) (.D 2 .zero)))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2], [2,1]]
  == some (.D 0 (.sum (.D 2 .zero) (.D 1 (.sum (.D 2 .zero) (.D 1 .zero)))))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2], [3,3], [2,1]]
  == some (.D 0 (.sum (.D 3 .zero) (.D 1 (.sum (.D 3 .zero) (.D 1 .zero)))))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2], [3,1], [3,1]]
  == some (.D 0 (.D 2 (.sum (.D 1 .zero) (.D 1 .zero))))
#guard Trans.Recal.oRB [[0,0], [1,1], [2,2], [1,1]]
  == some (.D 0 (.sum (.D 2 .zero) (.D 1 .zero)))

end

/-! ### §17.3 THE RULE READ OFF THE FAMILY DOES NOT GENERALISE

§17.1 and §17.2 describe what `oRB` does on a designed family.  Turning that description into
a closed form — rank the subscripts along the path, drop a node whose argument has nothing at
its own level or below, hoist-and-copy the summands above it — gives `encRule` below.  It is
WORSE than the reading it was meant to replace:

    380   top-level indices in §14's corpus (`topOKB`, non-empty)
    245   agree with `oR` under §15's naive `encB` (row-1 entry AS the subscript)
    114   agree under `encRule`

and its smallest failure is `(0,0)(1,1)(1,0)(2,1)`, four columns — a shape the family of
§17.1–§17.2 never contained, because that family was built out of single chains and one
sum, and this one has a `ψ₀` node inside an argument with a sibling after it.

SO THREE CANDIDATES ARE NOW EXCLUDED: `encB` (§15), `Dict.collapse` as the node function
(§16), and the family-derived rule (here).  What that says is not that a fourth is needed —
it is that reading `transPort` off measured families does not converge.  `transPort` is an
ALGORITHM (`Trans/Recal.lean` §3: seven case types, marks, memoisation), and the next honest
move is either to port it into `B`'s coordinates and prove the correspondence, or to give the
region a value that does not go through it at all and take the disagreement as a finding.

The measurements that survive all this are §14's: the value is a sum over the top-level
summands, and the node function is `ω^(Ω_{v-1} ⊕ ·)` exactly below `Ω_{v+1}`.  Those are
about `oR`'s VALUES, not about its algorithm, and nothing here touches them. -/

section
open TM TM.Term
open Trans.Dict (BT)

def rankOf (v : Nat) (P : List Nat) : Nat := ((P.filter (fun x => x < v)).eraseDups).length
def lvlBT : BT → Nat | .D u _ => u | _ => 0
def ofLBT : List BT → BT
  | [] => .zero
  | [a] => a
  | a :: rest => .sum a (ofLBT rest)

/-! §17.1–§17.2 の記述を閉じた形にしたもの。**反証済み** (下の `#guard`)。 -/
mutual
def encSumR : B → List Nat → List BT
  | .nil, _ => []
  | .nd v r a, P => encSumR r P ++ nodeRuleR v a P
def nodeRuleR (v : Nat) (a : B) (P : List Nat) : List BT :=
  let w := rankOf v P
  let R := encSumR a (v :: P)
  let H := R.takeWhile (fun x => lvlBT x > w)
  let L := R.drop H.length
  if !R.isEmpty && L.isEmpty then R else H ++ [.D w (ofLBT R)]
end

def encRule : B → BT
  | .nil => .zero
  | .nd v r a => ofLBT ((match encRule r with
      | .zero => [] | u => [u]) ++ [.D v (ofLBT (encSumR a [v, 0]))])

def encNaiveB : B → BT
  | .nil => .zero
  | .nd v .nil a => .D v (encNaiveB a)
  | .nd v r a => .sum (encNaiveB r) (.D v (encNaiveB a))

def topPop : List B := valCorpus.filter fun t => topOKB t && t != .nil

#guard topPop.length == 380
#guard (topPop.filter fun t => match Trans.oR (matB t 0) with
  | none => false | some u => u == Trans.Dict.dict (encNaiveB t)).length == 245
#guard (topPop.filter fun t => match Trans.oR (matB t 0) with
  | none => false | some u => u == Trans.Dict.dict (encRule t)).length == 114
-- 規則が外す最小の最上位行列。族には無かった形。
#guard Trans.Recal.oRB [[0,0], [1,1], [1,0], [2,1]]
  == some (.D 0 (.sum (.D 1 .zero) (.D 0 (.D 1 .zero))))

end

/-! ## §18 THE DECISION: PORT `transPort` — AND THE PORT, SCOPED

§15–§17 excluded three closed forms for the value, and the last one was WORSE than the naive
reading.  What they have in common is the method: read `transPort` off measured families.
That method does not converge, and the reason is structural — `transPort` is naruyoko's
`Trans`/`Mark` recursion (`Trans/Recal.lean` §3), and `Mark` is STATE.  `Trans M` alone is not
compositional; the pair `(Trans M, Mark M ·)` is, because `replMark` is what performs §17.2's
"hoist a summand out and keep a copy inside".  So the honest move is not a fourth candidate
but the port itself.

**The port is much smaller than the algorithm.**  Measured over the 380 top-level indices of
§14's corpus and the 714 distinct PREFIXES the recursion visits (every guard below):

    714 / 714   every visited prefix is ALREADY REDUCED — `red` never runs
        0       type -3 (reduce and retry)
       59       type -2 (not principal: split into `ppair` blocks)
        1       type -1 (one column)
        2       type  0 (`Trans (Pred M) = 0`)
      222 / 14 / 121 / 9 / 96 / 190     types 1 / 2 / 3 / 4 / 5 / 6

`red` is the largest single function in `Trans/Recal.lean` (`ppair`, `brF`, `firstNodes`,
`joints`, `incrFirst` and a fold with recursive calls), and on this region it is dead code.
What remains is the six node types plus two structural branches, and both of those branches
have an exact `B`-side description:

    ppair (matB t 0)  =  the top-level summands of `t`, verbatim
    fpar M 0 j 0      =  BMS's own `parent M 0 j`

**The second one is a theorem below**, not a measurement: `fpar0` scans leftward from `j-1`
for the first strictly shallower column and `BMS.parent M 0 j` takes the maximum of the same
set, so they agree on every matrix — the whole of `Evidence/Region.lean`'s parent machinery
and §8's `mem_iterParent0` (the chain is the left-minima) therefore apply to the algorithm
unchanged.  That is the bridge every remaining branch is built on: `fpar` appears in
`isParentP`, `isAnc`, `fAnc`, `ppair`, `isUnadmitted`, `trMax` and in types 1–6 themselves.

**AND THE PORT HAS A TEMPLATE IN THIS REPOSITORY.**  `Rows/Selected.lean` already opens the
`StateM` of `runAux` generically — `run_hit` (the memo table is hit), `run_base` (the bottom
`[(0,0)]`), `beq_PS_self` — and `Rows/G3.lean`, `Rows/G4.lean` and `Rows/G11.lean` each carry
a COMPLETE port for one infinite family: a specification `Val k req` that gives `Trans` and
`Mark` in one object, a memo invariant `Good`/`Sound` with `good_of_find`, and the induction
that adds one column.  That is exactly the "carry the mark" shape §17 was missing, written
out three times.  So the remaining work is to generalise it from a ladder to `B`, not to
invent a method.

**BOTH STRUCTURAL BRANCHES ARE NOW THEOREMS.**  §18.1 proves `fpar0 = BMS.parent`, and §18.3
proves `ppair (matB t 0) = (topSplit t).map (matB · 0)` — `ppairAux` cuts on `fAnc`'s last
element, `fAnc` is the row-0 parent chain (`fAnc_eq`), that chain is the left-minima (§8),
and on `matB` the left-minimum a summand's interior reaches is the summand's own root,
because the root sits at depth 0 and everything after it inside the summand is deeper.

WHAT IS NOT CLAIMED.  `red` being dead is measured here, not proved — that is next, and
`Rows/Ladder.lean` already carries the matrix-independent branch lemmas for it (`red_jj`,
`red_fold_open`, `red_fold_single`, `red_shift`, `red_head_one`).  Nothing in §13's
`expand_matB` depends on any of it. -/

section
open Trans.Recal

/-- 行列を対列へ (`ofMatrix` の本体)。 -/
def psM (M : Matrix) : PS := M.map (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int)))

/-- 添字の最上位の加数たち (左から)。 -/
def topSplit : B → List B
  | .nil => []
  | .nd v r a => topSplit r ++ [.nd v .nil a]

theorem getD_psM : ∀ (M : Matrix) (j : Nat),
    (psM M).getD j (0, 0) = ((ent M j 0 : Int), (ent M j 1 : Int)) := by
  intro M
  induction M with
  | nil => intro j; cases j <;> rfl
  | cons c cs ih => intro j; cases j with | zero => rfl | succ k => exact ih k

theorem psM_len (M : Matrix) : (psM M).length = M.length := List.length_map ..

theorem psM_gp0 (M : Matrix) (j : Nat) : gp0 (psM M) (j : Int) = (ent M j 0 : Int) := by
  show (if (j : Int) < 0 then 0 else ((psM M).getD (j : Int).toNat (0, 0)).1) = _
  rw [if_neg (by omega)]
  show ((psM M).getD j (0, 0)).1 = _
  rw [getD_psM]

theorem psM_gp1 (M : Matrix) (j : Nat) : gp1 (psM M) (j : Int) = (ent M j 1 : Int) := by
  show (if (j : Int) < 0 then 0 else ((psM M).getD (j : Int).toNat (0, 0)).2) = _
  rw [if_neg (by omega)]
  show ((psM M).getD j (0, 0)).2 = _
  rw [getD_psM]

/-- 領域の行列はアルゴリズムの定義域の中にある (高さ 2、空でない)。 -/
theorem ofMatrix_matB (t : B) (d : Nat) (h : t ≠ .nil) :
    ofMatrix (matB t d) = some (psM (matB t d)) := by
  have h1 : (matB t d).isEmpty = false := by
    have hp := matB_len_pos t d h
    cases hm : matB t d with
    | nil => rw [hm] at hp; exact absurd hp (by simp)
    | cons c cs => rfl
  have h2 : (matB t d).all (fun c => decide (c.length ≤ 2)) = true :=
    List.all_eq_true.mpr (fun c hc => by rw [matB_col_len t d c hc]; rfl)
  show (if (!(matB t d).isEmpty && (matB t d).all (fun c => decide (c.length ≤ 2)) : Bool)
        then some (psM (matB t d)) else none) = _
  rw [if_pos (by rw [h1, h2]; rfl)]

/-! ### §18.1 `fpar0` IS `BMS.parent` -/

theorem fpar0Aux_neg (f : Nat) (M : PS) (tgt j0 k : Int) (h : j0 < k) :
    fpar0Aux f M tgt j0 k = -1 := by
  cases f with
  | zero => rfl
  | succ g => show (if j0 < k then _ else _) = _; rw [if_pos h]

theorem max?_snoc (L : List Nat) (x : Nat) (h : ∀ y ∈ L, y ≤ x) :
    (L ++ [x]).max? = some x := by
  refine List.max?_eq_some_iff.mpr ⟨?_, ?_⟩
  · exact List.mem_append_right _ List.mem_cons_self
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact h b hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact Nat.le_refl _
      · exact absurd hb (by simp)

/-- 左向きの走査は「条件を満たす最大の添字」を返す。 -/
theorem fpar0Aux_spec (M : Matrix) (tgt : Nat) : ∀ (i f : Nat), i < f →
    fpar0Aux f (psM M) (tgt : Int) (i : Int) 0
      = (match ((List.range (i + 1)).filter (fun p => decide (ent M p 0 < tgt))).max? with
         | none => (-1 : Int) | some p => (p : Int)) := by
  intro i
  induction i with
  | zero =>
    intro f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    show (if ((0 : Nat) : Int) < 0 then (-1 : Int)
          else if gp0 (psM M) ((0 : Nat) : Int) < (tgt : Int) then ((0 : Nat) : Int)
          else fpar0Aux g (psM M) (tgt : Int) (((0 : Nat) : Int) - 1) 0) = _
    rw [if_neg (by omega), psM_gp0, fpar0Aux_neg g (psM M) _ _ _ (by omega)]
    show (if ((ent M 0 0 : Int) < (tgt : Int)) then ((0 : Nat) : Int) else (-1 : Int)) = _
    by_cases h : ent M 0 0 < tgt
    · rw [if_pos (by omega)]
      show (0 : Int) = _
      rw [show ((List.range 1).filter (fun p => decide (ent M p 0 < tgt))) = [0] from by
        simp [List.range_succ, h]]
      rfl
    · rw [if_neg (by omega)]
      rw [show ((List.range 1).filter (fun p => decide (ent M p 0 < tgt))) = [] from by
        simp [List.range_succ, h]]
      rfl
  | succ i ih =>
    intro f hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    show (if ((i + 1 : Nat) : Int) < 0 then (-1 : Int)
          else if gp0 (psM M) ((i + 1 : Nat) : Int) < (tgt : Int) then ((i + 1 : Nat) : Int)
          else fpar0Aux g (psM M) (tgt : Int) (((i + 1 : Nat) : Int) - 1) 0) = _
    rw [if_neg (by omega), psM_gp0,
      show (((i + 1 : Nat) : Int) - 1) = ((i : Nat) : Int) from by omega,
      ih g (by omega)]
    have hrange : ((List.range (i + 1 + 1)).filter (fun p => decide (ent M p 0 < tgt)))
        = ((List.range (i + 1)).filter (fun p => decide (ent M p 0 < tgt)))
          ++ (if ent M (i + 1) 0 < tgt then [i + 1] else []) := by
      rw [List.range_succ, List.filter_append]
      by_cases h : ent M (i + 1) 0 < tgt
      · rw [if_pos h]; simp [h]
      · rw [if_neg h]; simp [h]
    rw [hrange]
    by_cases h : ent M (i + 1) 0 < tgt
    · rw [if_pos (by omega : (ent M (i + 1) 0 : Int) < (tgt : Int)), if_pos h,
        max?_snoc _ _ (by
          intro y hy
          have := List.mem_range.mp (List.mem_filter.mp hy).1
          omega)]
    · rw [if_neg (by omega : ¬((ent M (i + 1) 0 : Int) < (tgt : Int))), if_neg h,
        List.append_nil]

/-- **アルゴリズムの行 0 の親は BMS の親。** どちらも「`j` より浅い直前の最大の列」。 -/
theorem fpar0_eq_parent (M : Matrix) (j : Nat) (hj : j < M.length) :
    fpar0 (psM M) (j : Int) 0
      = (match parent M 0 j with | none => (-1 : Int) | some p => (p : Int)) := by
  show (if (j : Int) < 0 ∨ (j : Int) ≥ lenI (psM M) then (-1 : Int)
        else fpar0Aux ((psM M).length + 1) (psM M) (gp0 (psM M) (j : Int)) ((j : Int) - 1) 0) = _
  rw [if_neg (by
    show ¬((j : Int) < 0 ∨ (j : Int) ≥ (((psM M).length : Nat) : Int))
    rw [psM_len]; omega), psM_gp0, psM_len]
  cases j with
  | zero =>
    rw [fpar0Aux_neg _ _ _ _ _ (by omega)]
    show (-1 : Int) = (match ((List.range 0).filter
      (fun p => decide (ent M p 0 < ent M 0 0))).max? with
      | none => (-1 : Int) | some p => (p : Int))
    rfl
  | succ i =>
    rw [show (((i + 1 : Nat) : Int) - 1) = ((i : Nat) : Int) from by omega,
      fpar0Aux_spec M (ent M (i + 1) 0) i (M.length + 1) (by omega)]
    rfl

/-- `fpar M 0 j k` は `fpar0 M j k` そのもの。 -/
theorem fpar_zero (M : PS) (j k : Int) : fpar M 0 j k = fpar0 M j k := by
  show (if j < 0 ∨ j ≥ lenI M then (-1 : Int)
        else if (0 : Nat) == 0 then fpar0Aux (M.length + 1) M (gp0 M j) (j - 1) k
        else fpar1Aux (M.length + 1) M (gp1 M j) j k) = _
  by_cases h : j < 0 ∨ j ≥ lenI M
  · rw [if_pos h]; show _ = (if j < 0 ∨ j ≥ lenI M then (-1 : Int) else _); rw [if_pos h]
  · rw [if_neg h]; show _ = (if j < 0 ∨ j ≥ lenI M then (-1 : Int) else _); rw [if_neg h]; rfl

/-- **§8 がそのままアルゴリズムに効く。** 親が返した列は左極小である。 -/
theorem lmin_of_fpar0 (M : Matrix) (j q : Nat) (hj : j < M.length)
    (h : fpar0 (psM M) (j : Int) 0 = (q : Int)) : LMin M q j := by
  rw [fpar0_eq_parent M j hj] at h
  have hp : parent M 0 j = some q := by
    cases hq : parent M 0 j with
    | none =>
      rw [hq] at h
      exact absurd (show (-1 : Int) = (q : Int) from h) (by omega)
    | some r =>
      rw [hq] at h
      have h' : ((r : Nat) : Int) = ((q : Nat) : Int) := h
      rw [show r = q from by omega]
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, show parent M 0 0 = none from rfl] at hp
    exact absurd hp (by simp)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine (mem_iterParent0 M (i + 1) (i + 1) q (Nat.le_refl _)).mp ?_
  rw [iterParent_cons hp]
  exact List.mem_cons_self

theorem ent_zero_of_ge_len (M : Matrix) (j : Nat) (h : M.length ≤ j) : ent M j 0 = 0 := by
  show ((M.getD j []).getD 0 0) = 0
  rw [show M.getD j [] = [] from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]]
  rfl

theorem parent0_none_of_zero (M : Matrix) (s : Nat) (h : ent M s 0 = 0) :
    parent M 0 s = none := by
  refine List.max?_eq_none_iff.mpr ?_
  refine List.filter_eq_nil_iff.mpr ?_
  intro p _
  rw [h]
  simp

/-- 自分より浅い列が前に無いなら親は無い。 -/
theorem parent0_none_of_min (M : Matrix) (s : Nat) (h : ∀ i, i < s → ent M s 0 ≤ ent M i 0) :
    parent M 0 s = none := by
  refine List.max?_eq_none_iff.mpr (List.filter_eq_nil_iff.mpr ?_)
  intro p hp
  have := h p (List.mem_range.mp hp)
  simp
  omega

theorem getLast?_cons_of_ne_nil {α : Type _} (a : α) : ∀ (l : List α), l ≠ [] →
    (a :: l).getLast? = l.getLast?
  | [], h => absurd rfl h
  | _ :: _, _ => List.getLast?_cons_cons

/-- **親鎖の終点は、親を持たない最初の列。** -/
theorem iterParent0_last (M : Matrix) (s : Nat) (hs : parent M 0 s = none) :
    ∀ (fuel x : Nat), x ≤ fuel → s < x → LMin M s x →
      (iterParent (parent M 0) fuel x).getLast? = some s := by
  intro fuel
  induction fuel with
  | zero => intro x hx hsx _; omega
  | succ g ih =>
    intro x hx hsx hlm
    have hsx0 : ent M s 0 < ent M x 0 := hlm.2 x hsx (Nat.le_refl x)
    have hmem : s ∈ (List.range x).filter (fun p => decide (ent M p 0 < ent M x 0)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hsx, decide_eq_true hsx0⟩
    cases hr : parent M 0 x with
    | none =>
      exfalso
      have := List.max?_eq_none_iff.mp hr
      rw [this] at hmem
      exact absurd hmem (by simp)
    | some r =>
      obtain ⟨hrm, hrmax⟩ := List.max?_eq_some_iff.mp hr
      have hrx : r < x := List.mem_range.mp (List.mem_filter.mp hrm).1
      have hsr : s ≤ r := hrmax s hmem
      rw [iterParent_cons hr]
      rcases Nat.eq_or_lt_of_le hsr with rfl | hlt
      · rw [iterParent_nil hs]
        rfl
      · have hrest : (iterParent (parent M 0) g r).getLast? = some s :=
          ih r (by omega) hlt ⟨hlt, fun p h1 h2 => hlm.2 p h1 (by omega)⟩
        rw [getLast?_cons_of_ne_nil r _ (by
          intro hnil
          rw [hnil] at hrest
          exact absurd hrest (by simp))]
        exact hrest

/-- **`fAnc` は行 0 の親鎖そのもの。** -/
theorem fAncAux_eq (M : Matrix) : ∀ (f x : Nat), x ≤ f → x < M.length →
    ∀ (acc : List Int),
      fAncAux f (psM M) 0 (x : Int) 0 acc
        = acc ++ (iterParent (parent M 0) f x).map (fun (q : Nat) => (q : Int)) := by
  intro f
  induction f with
  | zero =>
    intro x _ _ acc
    show acc = _
    rw [show iterParent (parent M 0) 0 x = [] from rfl, List.map_nil, List.append_nil]
  | succ g ih =>
    intro x hx hlen acc
    have hfp : fpar (psM M) 0 (x : Int) 0
        = (match parent M 0 x with | none => (-1 : Int) | some p => (p : Int)) := by
      rw [fpar_zero, fpar0_eq_parent M x hlen]
    show (let j1 := fpar (psM M) 0 (x : Int) 0
          if j1 ≥ 0 then fAncAux g (psM M) 0 j1 0 (acc ++ [j1]) else acc) = _
    rw [hfp]
    cases hr : parent M 0 x with
    | none =>
      rw [iterParent_nil hr]
      show (if ((-1 : Int) ≥ 0) then _ else acc) = _
      rw [if_neg (by omega), List.map_nil, List.append_nil]
    | some r =>
      have hrx : r < x := by
        obtain ⟨hrm, _⟩ := List.max?_eq_some_iff.mp hr
        exact List.mem_range.mp (List.mem_filter.mp hrm).1
      rw [iterParent_cons hr]
      show (if (((r : Nat) : Int) ≥ 0) then
              fAncAux g (psM M) 0 ((r : Nat) : Int) 0 (acc ++ [((r : Nat) : Int)]) else acc) = _
      rw [if_pos (by omega), ih r (by omega) (by omega) (acc ++ [((r : Nat) : Int)]),
        List.map_cons, List.append_assoc]
      rfl

theorem fAnc_eq (M : Matrix) (x : Nat) (hlen : x < M.length) :
    fAnc (psM M) 0 (x : Int) 0
      = ((x : Nat) : Int)
        :: (iterParent (parent M 0) ((psM M).length + 1) x).map (fun (q : Nat) => (q : Int)) := by
  show (if (x : Int) < 0 ∨ (x : Int) ≥ lenI (psM M) then ([] : List Int)
        else fAncAux ((psM M).length + 1) (psM M) 0 (x : Int) 0 [(x : Int)]) = _
  rw [if_neg (by
    show ¬((x : Int) < 0 ∨ (x : Int) ≥ (((psM M).length : Nat) : Int))
    rw [psM_len]; omega),
    fAncAux_eq M ((psM M).length + 1) x (by rw [psM_len]; omega) hlen [(x : Int)]]
  rfl

/-- **ブロックの根に達する。** 深さ 0 の列 `s` が `x` の左極小なら `fAnc` の終点は `s`。 -/
theorem fAnc_last (M : Matrix) (s x : Nat) (hs : parent M 0 s = none) (hlen : x < M.length)
    (hsx : s < x) (hlm : LMin M s x) :
    ((fAnc (psM M) 0 (x : Int) 0).getLast?).getD 0 = ((s : Nat) : Int) := by
  rw [fAnc_eq M x hlen]
  have hch : (iterParent (parent M 0) ((psM M).length + 1) x).getLast? = some s :=
    iterParent0_last M s hs ((psM M).length + 1) x (by rw [psM_len]; omega) hsx hlm
  have hne : (iterParent (parent M 0) ((psM M).length + 1) x) ≠ [] := by
    intro hnil; rw [hnil] at hch; exact absurd hch (by simp)
  rw [getLast?_cons_of_ne_nil _ _ (by
    intro hnil
    exact hne (List.map_eq_nil_iff.mp hnil)),
    List.getLast?_map, hch]
  rfl

/-- 自分が深さ 0 なら `fAnc` の終点は自分。 -/
theorem fAnc_last_self (M : Matrix) (x : Nat) (hs : parent M 0 x = none) (hlen : x < M.length) :
    ((fAnc (psM M) 0 (x : Int) 0).getLast?).getD 0 = ((x : Nat) : Int) := by
  rw [fAnc_eq M x hlen, iterParent_nil hs]
  rfl

/-! ### §18.2 THE SCOPING MEASUREMENT

`Trans.oR` is candidate tier and appears in no justification; these are measurements. -/

/-- 再帰が実際に訪れる接頭辞 (領域の 380 個の添字から)。 -/
def visitedPS : List PS :=
  (topPop.flatMap fun t =>
    let M := psM (matB t 0)
    (List.range M.length).map (fun k => M.take (k + 1))).eraseDups

/-- 場合分けの型 (`Trans/Recal.lean` §3 の `TransType`)。 -/
def tyOf (M : PS) : Int :=
  let j1 : Int := lenI M - 1
  if !(isReducedP M) then -3
  else if j1 == 0 then -1
  else if !(isPrincipalP M) then -2
  else if transPort (predP M) == Trans.Dict.BT.zero then 0
  else Int.ofNat (transTypeMain M (fpar M 0 j1 0) j1)

#guard visitedPS.length == 714
-- **`red` は一度も走らない。**
#guard visitedPS.all isReducedP
-- 型ごとの数 (-3 から 6 まで)。
#guard (List.range 10).map (fun k => (visitedPS.filter fun M => tyOf M == (Int.ofNat k) - 3).length)
  == [0, 59, 1, 2, 222, 14, 121, 9, 96, 190]

/-! ### §18.3 `ppair` IS THE TOP-LEVEL SPLIT

The second structural branch, now a theorem too.  `ppairAux` walks leftward from the last
column: it takes `fAnc`'s last element as the block root, cuts the slice from there, and
restarts one column further left.  §18.1 makes `fAnc` the row-0 parent chain (`fAnc_eq`),
§8 makes that chain the left-minima, and on `matB` the blocks are exactly the top-level
summands — each starts at depth 0 and everything after it inside the summand is deeper
(`matB_col_lb`).  So the chain from anywhere inside a summand ends at that summand's own
root, which is what `ppairAux` cuts on. -/

theorem matB_topSplit : ∀ (t : B) (d : Nat),
    matB t d = ((topSplit t).map (fun s => matB s d)).flatten := by
  intro t
  induction t with
  | nil => intro d; rfl
  | nd v r a ihr _ =>
    intro d
    show matB r d ++ ([d, v] :: matB a (d + 1))
      = ((topSplit r ++ [B.nd v .nil a]).map (fun s => matB s d)).flatten
    rw [List.map_append, List.flatten_append, ← ihr d]
    simp
    rfl

/-- ブロック: 先頭が深さ 0、以降はすべて深い。 -/
def IsBlk (Bk : Matrix) : Prop :=
  0 < Bk.length ∧ ent Bk 0 0 = 0 ∧ ∀ p, 0 < p → p < Bk.length → 0 < ent Bk p 0

theorem isBlk_node (v : Nat) (a : B) : IsBlk (matB (.nd v .nil a) 0) := by
  refine ⟨matB_len_pos (.nd v .nil a) 0 (by intro h; exact B.noConfusion h), rfl, ?_⟩
  intro p hp hlen
  obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
  have hi : i < (matB a 1).length := by
    have h2 : (([0, v] : Col) :: matB a 1).length = (matB a 1).length + 1 := by simp
    show i < (matB a 1).length
    have h3 : (matB (B.nd v .nil a) 0).length = (matB a 1).length + 1 := h2
    omega
  have hlb := matB_col_lb a 1 _ (getD_mem (matB a 1) [] i hi)
  show 0 < ent (matB a 1) i 0
  exact Nat.lt_of_lt_of_le (by omega) hlb

theorem isBlk_of_mem_topSplit : ∀ (t s : B), s ∈ topSplit t → IsBlk (matB s 0) := by
  intro t
  induction t with
  | nil => intro s h; exact absurd (show s ∈ ([] : List B) from h) (by simp)
  | nd v r a ihr _ =>
    intro s h
    rcases List.mem_append.mp h with h | h
    · exact ihr s h
    · rcases List.mem_cons.mp h with rfl | h
      · exact isBlk_node v a
      · exact absurd (show s ∈ ([] : List B) from h) (by simp)

theorem psM_append (X Y : Matrix) : psM (X ++ Y) = psM X ++ psM Y := List.map_append ..

theorem slice_block (X Bk P : Matrix) :
    slice (psM (X ++ (Bk ++ P))) ((X.length : Nat) : Int)
        ((X.length + Bk.length : Nat) : Int) = psM Bk := by
  show ((psM (X ++ (Bk ++ P))).drop ((X.length : Nat) : Int).toNat).take
    (((X.length + Bk.length : Nat) : Int) - ((X.length : Nat) : Int)).toNat = _
  rw [show (((X.length + Bk.length : Nat) : Int) - ((X.length : Nat) : Int)).toNat
      = Bk.length from by omega,
    show ((X.length : Nat) : Int).toNat = X.length from rfl,
    psM_append X (Bk ++ P), ← psM_len X,
    show ((psM X ++ psM (Bk ++ P)).drop (psM X).length) = psM (Bk ++ P) from by simp,
    psM_append Bk P, ← psM_len Bk,
    show ((psM Bk ++ psM P).take (psM Bk).length) = psM Bk from by simp]

theorem len_le_flatten_len : ∀ (Bs : List Matrix), (∀ Bk ∈ Bs, IsBlk Bk) →
    Bs.length ≤ Bs.flatten.length := by
  intro Bs
  induction Bs with
  | nil => intro _; simp
  | cons X Xs ihx =>
    intro hb
    have hX : 0 < X.length := (hb X (by simp)).1
    have := ihx (fun Y hY => hb Y (by simp [hY]))
    rw [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- **`ppair` はブロックの並びをそのまま返す。** -/
theorem ppairAux_blocks : ∀ (f : Nat) (Bs : List Matrix) (P : Matrix) (acc : List PS),
    (∀ Bk ∈ Bs, IsBlk Bk) → Bs.length ≤ f →
    ppairAux f (psM (Bs.flatten ++ P)) ((Bs.flatten.length : Int) - 1) acc
      = Bs.map psM ++ acc := by
  intro f
  induction f with
  | zero =>
    intro Bs P acc _ hlen
    have : Bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ g ih =>
    intro Bs P acc hb hlen
    rcases List.eq_nil_or_concat Bs with rfl | ⟨Bs', Bk, hcon⟩
    · show (if ((([] : List Matrix).flatten.length : Int) - 1) < 0 then acc else _) = _
      rw [if_pos (by simp)]
      rfl
    · rw [show Bs = Bs' ++ [Bk] from by rw [hcon, List.concat_eq_append]] at hb hlen ⊢
      have hBk : IsBlk Bk := hb Bk (by simp)
      have hb' : ∀ X ∈ Bs', IsBlk X := fun X hX => hb X (by simp [hX])
      have hpos : 0 < Bk.length := hBk.1
      have hflat : (Bs' ++ [Bk]).flatten = Bs'.flatten ++ Bk := by
        rw [List.flatten_append]; simp
      have hM : (Bs' ++ [Bk]).flatten ++ P = Bs'.flatten ++ (Bk ++ P) := by
        rw [hflat, List.append_assoc]
      have hlenf : ((Bs' ++ [Bk]).flatten.length : Int)
          = ((Bs'.flatten.length + Bk.length : Nat) : Int) := by
        rw [hflat, List.length_append]
      have hMlen : ((Bs' ++ [Bk]).flatten ++ P).length
          = Bs'.flatten.length + Bk.length + P.length := by
        rw [hflat, List.length_append, List.length_append]
      have hentR : ∀ i, Bs'.flatten.length ≤ i →
          ent ((Bs' ++ [Bk]).flatten ++ P) i 0
            = ent (Bk ++ P) (i - Bs'.flatten.length) 0 := by
        intro i hi; rw [hM]; exact ent_append _ _ i 0 hi
      have hentBk : ∀ i, i < Bk.length → ent (Bk ++ P) i 0 = ent Bk i 0 :=
        fun i hi => ent_append_left _ _ i 0 hi
      have hroot : ent ((Bs' ++ [Bk]).flatten ++ P) Bs'.flatten.length 0 = 0 := by
        rw [hentR Bs'.flatten.length (Nat.le_refl _),
          show Bs'.flatten.length - Bs'.flatten.length = 0 from by omega,
          hentBk 0 hpos, hBk.2.1]
      have hj1 : Bs'.flatten.length + Bk.length - 1
          < ((Bs' ++ [Bk]).flatten ++ P).length := by rw [hMlen]; omega
      have hfa : ((fAnc (psM ((Bs' ++ [Bk]).flatten ++ P)) 0
          ((Bs'.flatten.length + Bk.length - 1 : Nat) : Int) 0).getLast?).getD 0
            = ((Bs'.flatten.length : Nat) : Int) := by
        rcases Nat.lt_or_ge Bs'.flatten.length (Bs'.flatten.length + Bk.length - 1)
          with hlt | hge
        · refine fAnc_last _ Bs'.flatten.length _ (parent0_none_of_zero _ _ hroot)
            hj1 hlt ⟨hlt, ?_⟩
          intro p h1 h2
          rw [hroot, hentR p (by omega), hentBk (p - Bs'.flatten.length) (by omega)]
          exact hBk.2.2 (p - Bs'.flatten.length) (by omega) (by omega)
        · have heq : Bs'.flatten.length + Bk.length - 1 = Bs'.flatten.length := by omega
          rw [heq]
          exact fAnc_last_self _ Bs'.flatten.length (parent0_none_of_zero _ _ hroot)
            (by rw [heq] at hj1; exact hj1)
      show (if (((Bs' ++ [Bk]).flatten.length : Int) - 1) < 0 then acc
            else ppairAux g (psM ((Bs' ++ [Bk]).flatten ++ P))
              (((fAnc (psM ((Bs' ++ [Bk]).flatten ++ P)) 0
                  (((Bs' ++ [Bk]).flatten.length : Int) - 1) 0).getLast?).getD 0 - 1)
              (slice (psM ((Bs' ++ [Bk]).flatten ++ P))
                (((fAnc (psM ((Bs' ++ [Bk]).flatten ++ P)) 0
                  (((Bs' ++ [Bk]).flatten.length : Int) - 1) 0).getLast?).getD 0)
                ((((Bs' ++ [Bk]).flatten.length : Int) - 1) + 1) :: acc)) = _
      rw [hlenf, if_neg (by omega),
        show (((Bs'.flatten.length + Bk.length : Nat) : Int) - 1)
          = ((Bs'.flatten.length + Bk.length - 1 : Nat) : Int) from by omega,
        hfa,
        show ((Bs'.flatten.length + Bk.length - 1 : Nat) : Int) + 1
          = ((Bs'.flatten.length + Bk.length : Nat) : Int) from by omega,
        hM, slice_block Bs'.flatten Bk P,
        ih Bs' (Bk ++ P) (psM Bk :: acc) hb' (by
          rw [List.length_append] at hlen; simp at hlen ⊢; omega)]
      simp

theorem ppair_blocks (Bs : List Matrix) (hb : ∀ Bk ∈ Bs, IsBlk Bk) :
    ppair (psM Bs.flatten) = Bs.map psM := by
  show ppairAux ((psM Bs.flatten).length + 1) (psM Bs.flatten)
    (lenI (psM Bs.flatten) - 1) [] = _
  rw [show lenI (psM Bs.flatten) = ((Bs.flatten.length : Nat) : Int) from by
      show (((psM Bs.flatten).length : Nat) : Int) = _
      rw [psM_len],
    show (psM Bs.flatten) = psM (Bs.flatten ++ []) from by rw [List.append_nil],
    ppairAux_blocks _ Bs [] [] hb (by
      rw [List.append_nil, psM_len]
      exact Nat.le_trans (len_le_flatten_len Bs hb) (by omega))]
  simp

/-- **領域の `ppair` は最上位の加数そのもの。** 型 -2 の枝の `B` 側の記述である。 -/
theorem ppair_matB (t : B) :
    ppair (psM (matB t 0)) = (topSplit t).map (fun s => psM (matB s 0)) := by
  have hb : ∀ Bk ∈ (topSplit t).map (fun s => matB s 0), IsBlk Bk := by
    intro Bk hBk
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hBk
    exact isBlk_of_mem_topSplit t s hs
  have hpb := ppair_blocks ((topSplit t).map (fun s => matB s 0)) hb
  rw [← matB_topSplit t 0] at hpb
  rw [hpb, List.map_map]
  rfl

end

/-! ## §19 THE NORMAL FORM: A NODE'S LEVEL IS AT MOST ITS PARENT'S PLUS ONE

§18 measured that `red` never runs on the region's 380 indices.  That is NOT a property of
`topOKB`: enumerate every index with at most 4 nodes and levels below 3 and only **101 of
220** are reduced.  So the port's gate is not "`red` is dead on `matB` matrices" — it is a
NORMAL FORM, and this section finds it and proves what the region needs of it.

    nfB t   ⟺   every node's level is at most its parent's level plus one
                (a top-level node's parent is nothing, so its level must be 0)

MEASURED, and the agreement is exact — not approximate — on every index of three
enumerations:

    levels < 3, ≤ 4 nodes      220 indices     220 / 220 agree   (101 reduced)
    levels < 4, ≤ 5 nodes     5101 indices    5101 / 5101 agree  (697 reduced)
    levels < 3, ≤ 6 nodes    16332 indices   16332 / 16332 agree

    nfB t  =  isReducedP (psM (matB t 0))

The smallest failure is `(0,0)(1,2)`, which `red` sends to `(0,0)(1,1)`: a level-2 node
directly under a level-0 one is a level jump, and `red` closes it.  The rule is LOCAL — the
parent alone, not the ancestors.  The variant "at most one more than the largest ancestor
level" is refuted by `(0,0)(1,1)(2,0)(3,2)`, which has a level-1 ancestor and is still not
reduced: `red` sends it to `(0,0)(1,1)(2,0)(3,1)`.

`topOKB` is exactly the top-level half of `nfB` (`topOKB_of_nfB`), so the region loses
nothing by strengthening its hypothesis, and it gains the gate.

**WHAT IS PROVED HERE.**  `nfLe` is preserved by every operator the fundamental sequence is
built from — `appB`, `plugB`, `repNode`, `repB`, `iterD`, `rwB` — and therefore

    nfB t → nfB (fsB t n)

which with §13's `expand_matB` gives `Hclosed` for the FULL generalised region (`hclosedB`).
That is `certIn_region`'s first supply, discharged for the region `B` describes rather than
for `Evidence/RegionV.lean`'s `A` fragment.

The interesting step is `iterD`: `rwB` iterates at the nearest ancestor of level below `w`,
so the node it plugs into has level `≥ w > v`, and `lastBnd_ge` turns "no ancestor of the
last node has level below `w`" into the bound that keeps the copies in normal form.

WHAT IS NOT CLAIMED.  `nfB = isReducedP` is measured, not proved; that equality is the port's
gate and is the next brick.  What §19 proves is everything the REGION needs of `nfB`. -/

section
open Trans.Recal

/-- **標準形。** 節の段は親の段 + 1 以下。`m` はその位置で許される上限。 -/
def nfLe (m : Nat) : B → Bool
  | .nil => true
  | .nd v r a => decide (v ≤ m) && nfLe m r && nfLe (v + 1) a

/-- 最上位の節の親は無いので、その段は 0 でなければならない。 -/
def nfB (t : B) : Bool := nfLe 0 t

theorem nfLe_nd_iff (m v : Nat) (r a : B) :
    nfLe m (.nd v r a) = true ↔ (v ≤ m ∧ nfLe m r = true ∧ nfLe (v + 1) a = true) := by
  show (decide (v ≤ m) && nfLe m r && nfLe (v + 1) a) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, and_assoc]

theorem nfLe_mono : ∀ (t : B) (m m' : Nat), m ≤ m' → nfLe m t = true → nfLe m' t = true := by
  intro t
  induction t with
  | nil => intro _ _ _ _; rfl
  | nd v r a ihr _ =>
    intro m m' hm h
    obtain ⟨h1, h2, h3⟩ := (nfLe_nd_iff m v r a).mp h
    exact (nfLe_nd_iff m' v r a).mpr ⟨by omega, ihr m m' hm h2, h3⟩

/-- **`topOKB` は `nfB` の最上位の半分。** -/
theorem topOKB_of_nfB : ∀ (t : B), nfB t = true → topOKB t = true := by
  intro t
  show nfLe 0 t = true → _
  induction t with
  | nil => intro _; rfl
  | nd v r a ihr _ =>
    intro h
    obtain ⟨h1, h2, _⟩ := (nfLe_nd_iff 0 v r a).mp h
    show ((v == 0) && topOKB r) = true
    rw [show (v == 0) = true from decide_eq_true (by omega), ihr h2]
    rfl

/-! ### §19.1 EVERY OPERATOR OF THE FUNDAMENTAL SEQUENCE PRESERVES IT -/

theorem nfLe_appB : ∀ (s r : B) (m : Nat), nfLe m r = true → nfLe m s = true →
    nfLe m (appB r s) = true := by
  intro s
  induction s with
  | nil => intro r m hr _; exact hr
  | nd v s a ihs _ =>
    intro r m hr hs
    obtain ⟨h1, h2, h3⟩ := (nfLe_nd_iff m v s a).mp hs
    exact (nfLe_nd_iff m v (appB r s) a).mpr ⟨h1, ihs r m hr h2, h3⟩

/-- 最後の節の位置で許される上限。 -/
def lastBnd (m : Nat) : B → Nat
  | .nil => m
  | .nd _ _ .nil => m
  | .nd v _ a => lastBnd (v + 1) a

theorem nfLe_plugB : ∀ (a : B) (m : Nat) (y : B), nfLe m a = true →
    nfLe (lastBnd m a) y = true → nfLe m (plugB a y) = true := by
  intro a
  induction a with
  | nil => intro m y _ _; rfl
  | nd v r a _ iha =>
    intro m y ha hy
    obtain ⟨h1, h2, h3⟩ := (nfLe_nd_iff m v r a).mp ha
    cases a with
    | nil =>
      show nfLe m (appB r y) = true
      exact nfLe_appB y r m h2 hy
    | nd u s b =>
      show nfLe m (.nd v r (plugB (.nd u s b) y)) = true
      refine (nfLe_nd_iff m v r _).mpr ⟨h1, h2, iha (v + 1) y h3 ?_⟩
      exact hy

/-- 祖先の段がすべて `w` 以上なら、最後の節の上限も `w` 以上。 -/
theorem lastBnd_ge : ∀ (a : B) (w m : Nat), hasLowAnc w a = false → w ≤ m →
    w ≤ lastBnd m a := by
  intro a
  induction a with
  | nil => intro w m _ hm; exact hm
  | nd v r b _ ihb =>
    intro w m hlow hm
    cases b with
    | nil => exact hm
    | nd u s c =>
      have hb : (decide (v < w) || hasLowAnc w (.nd u s c)) = false := hlow
      have h1 : decide (v < w) = false := by
        cases hd : decide (v < w) with
        | false => rfl
        | true => rw [hd] at hb; exact absurd hb (by simp)
      have h2 : hasLowAnc w (.nd u s c) = false := by
        cases hd : hasLowAnc w (.nd u s c) with
        | false => rfl
        | true => rw [hd] at hb; exact absurd hb (by simp)
      have hvw : w ≤ v := by have := of_decide_eq_false h1; omega
      show w ≤ lastBnd (v + 1) (.nd u s c)
      exact ihb w (v + 1) h2 (by omega)

theorem nfLe_iterD : ∀ (k : Nat) (v : Nat) (a : B) (m : Nat), v ≤ m →
    nfLe (v + 1) a = true → v ≤ lastBnd (v + 1) a →
    nfLe m (iterD v a k) = true := by
  intro k
  induction k with
  | zero =>
    intro v a m hvm ha hlb
    refine (nfLe_nd_iff m v .nil _).mpr ⟨hvm, rfl, ?_⟩
    exact nfLe_plugB a (v + 1) .nil ha rfl
  | succ j ih =>
    intro v a m hvm ha hlb
    refine (nfLe_nd_iff m v .nil _).mpr ⟨hvm, rfl, ?_⟩
    exact nfLe_plugB a (v + 1) _ ha (ih v a (lastBnd (v + 1) a) hlb ha hlb)

theorem nfLe_repNode : ∀ (k : Nat) (v : Nat) (P : B) (m : Nat), v ≤ m →
    nfLe (v + 1) P = true → nfLe m (repNode v P k) = true := by
  intro k
  induction k with
  | zero => intro v P m hvm hP; exact (nfLe_nd_iff m v .nil P).mpr ⟨hvm, rfl, hP⟩
  | succ j ih =>
    intro v P m hvm hP
    exact (nfLe_nd_iff m v _ P).mpr ⟨hvm, ih v P m hvm hP, hP⟩

theorem nfLe_repB : ∀ (t : B) (m n : Nat), nfLe m t = true → nfLe m (repB t n) = true := by
  intro t
  induction t with
  | nil => intro _ _ _; rfl
  | nd v r a _ iha =>
    intro m n h
    obtain ⟨h1, h2, h3⟩ := (nfLe_nd_iff m v r a).mp h
    cases a with
    | nil => exact rfl
    | nd u P c =>
      cases u with
      | zero =>
        cases c with
        | nil =>
          show nfLe m (appB r (repNode v P n)) = true
          obtain ⟨_, hP, _⟩ := (nfLe_nd_iff (v + 1) 0 P .nil).mp h3
          exact nfLe_appB _ r m h2 (nfLe_repNode n v P m h1 hP)
        | nd u2 s2 c2 =>
          show nfLe m (.nd v r (repB (.nd 0 P (.nd u2 s2 c2)) n)) = true
          exact (nfLe_nd_iff m v r _).mpr ⟨h1, h2, iha (v + 1) n h3⟩
      | succ u' =>
        show nfLe m (.nd v r (repB (.nd (u' + 1) P c) n)) = true
        exact (nfLe_nd_iff m v r _).mpr ⟨h1, h2, iha (v + 1) n h3⟩

theorem nfLe_rwB : ∀ (t : B) (w n m : Nat), nfLe m t = true → nfLe m (rwB w n t) = true := by
  intro t
  induction t with
  | nil => intro _ _ _ _; rfl
  | nd v r a _ iha =>
    intro w n m h
    obtain ⟨h1, h2, h3⟩ := (nfLe_nd_iff m v r a).mp h
    cases a with
    | nil => exact h
    | nd u s b =>
      show nfLe m (if hasLowAnc w (.nd u s b) then .nd v r (rwB w n (.nd u s b))
        else if v < w then appB r (iterD v (.nd u s b) n) else .nd v r (.nd u s b)) = true
      by_cases hl : hasLowAnc w (.nd u s b) = true
      · rw [if_pos hl]
        exact (nfLe_nd_iff m v r _).mpr ⟨h1, h2, iha w n (v + 1) h3⟩
      · rw [if_neg hl]
        have hl' : hasLowAnc w (.nd u s b) = false := by
          cases hd : hasLowAnc w (.nd u s b) with
          | false => rfl
          | true => exact absurd hd hl
        by_cases hv : v < w
        · rw [if_pos hv]
          refine nfLe_appB _ r m h2 (nfLe_iterD n v (.nd u s b) m h1 h3 ?_)
          cases b with
          | nil => show v ≤ v + 1; omega
          | nd u2 s2 c2 =>
            have hb : (decide (u < w) || hasLowAnc w (.nd u2 s2 c2)) = false := hl'
            have hu : decide (u < w) = false := by
              cases hd : decide (u < w) with
              | false => rfl
              | true => rw [hd] at hb; exact absurd hb (by simp)
            have h2' : hasLowAnc w (.nd u2 s2 c2) = false := by
              cases hd : hasLowAnc w (.nd u2 s2 c2) with
              | false => rfl
              | true => rw [hd] at hb; exact absurd hb (by simp)
            have huw : w ≤ u := by have := of_decide_eq_false hu; omega
            have := lastBnd_ge (.nd u2 s2 c2) w (u + 1) h2' (by omega)
            show v ≤ lastBnd (u + 1) (.nd u2 s2 c2)
            omega
        · rw [if_neg hv]
          exact h

/-- **標準形は基本列で閉じている。** -/
theorem nfB_fsB (t : B) (n : Nat) (h : nfB t = true) : nfB (fsB t n) = true := by
  show nfLe 0 (fsB t n) = true
  have h0 : nfLe 0 t = true := h
  cases t with
  | nil => exact rfl
  | nd v r a =>
    obtain ⟨h1, h2, h3⟩ := (nfLe_nd_iff 0 v r a).mp h0
    cases v with
    | zero =>
      cases a with
      | nil => exact h2
      | nd u s b =>
        show nfLe 0 (if (lastLvl (.nd u s b) == 0) = true
          then repB (.nd 0 r (.nd u s b)) n
          else rwB (lastLvl (.nd u s b)) n (.nd 0 r (.nd u s b))) = true
        by_cases hz : (lastLvl (.nd u s b) == 0) = true
        · rw [if_pos hz]; exact nfLe_repB _ 0 n h0
        · rw [if_neg hz]; exact nfLe_rwB _ _ n 0 h0
    | succ v' =>
      cases a with
      | nil => exact rfl
      | nd u s b =>
        show nfLe 0 (if (lastLvl (.nd u s b) == 0) = true
          then repB (.nd (v' + 1) r (.nd u s b)) n
          else rwB (lastLvl (.nd u s b)) n (.nd (v' + 1) r (.nd u s b))) = true
        by_cases hz : (lastLvl (.nd u s b) == 0) = true
        · rw [if_pos hz]; exact nfLe_repB _ 0 n h0
        · rw [if_neg hz]; exact nfLe_rwB _ _ n 0 h0

/-! ### §19.2 `Hclosed` FOR THE FULL GENERALISED REGION -/

/-- 一般化した領域: 標準形の添字の行列。 -/
def RegB (S : Matrix) : Prop := ∃ t : B, nfB t = true ∧ S = matB t 0

/-- **`certIn_region` の第 1 供給、一般化した領域で。** -/
theorem hclosedB : ∀ (S : Matrix), RegB S → ∀ (n : Nat), RegB (BMS.expand S n) := by
  rintro S ⟨t, hnf, rfl⟩ n
  cases t with
  | nil =>
    refine ⟨.nil, rfl, ?_⟩
    show (BMS.expand? [] n).getD [] = []
    rfl
  | nd v r a =>
    refine ⟨fsB (.nd v r a) n, nfB_fsB _ n hnf, ?_⟩
    show (BMS.expand? (matB (B.nd v r a) 0) n).getD [] = _
    rw [expand_matB (.nd v r a) (topOKB_of_nfB _ hnf) (by intro h; exact B.noConfusion h) n]
    rfl

/-! ### §19.3 THE MEASUREMENT: `nfB` IS EXACTLY `isReducedP`

`Trans.Recal.red` is the reference implementation's reduction, ported in `Trans/Recal.lean`;
these are measurements over exhaustive enumerations, not a proof. -/

/-- 節が `n` 個以下、段が `L` 未満の `B` を全部。 -/
partial def enumNodes (L : Nat) : Nat → List B
  | 0 => [.nil]
  | n + 1 =>
    (List.range (n + 1)).flatMap fun k =>
      (enumNodes L k).flatMap fun r =>
        (enumNodes L (n - k)).flatMap fun a =>
          (List.range L).map fun v => B.nd v r a

def enumB (L n : Nat) : List B :=
  ((List.range (n + 1)).flatMap (enumNodes L)).filter fun t => topOKB t && t != .nil

#guard (enumB 3 4).length == 220
#guard ((enumB 3 4).filter fun t => isReducedP (psM (matB t 0))).length == 101
#guard (enumB 3 4).all fun t => nfB t == isReducedP (psM (matB t 0))
#guard (enumB 4 5).length == 5101
#guard (enumB 4 5).all fun t => nfB t == isReducedP (psM (matB t 0))
#guard (enumB 3 6).length == 16332
#guard (enumB 3 6).all fun t => nfB t == isReducedP (psM (matB t 0))
-- 最小の失敗と、局所的でない変種の反例。
#guard redP (psM [[0, 0], [1, 2]]) == psM [[0, 0], [1, 1]]
#guard redP (psM [[0, 0], [1, 1], [2, 0], [3, 2]]) == psM [[0, 0], [1, 1], [2, 0], [3, 1]]
-- 領域の母集団はすべて標準形。
#guard topPop.all nfB

end

/-! ## §20 WHAT `red` DOES TO A `matB` MATRIX, PINNED

§19 found the normal form and measured `nfB = isReducedP`.  Proving that equality means
computing `red` on `matB` matrices, and `red`'s own recursion descends into SUBTREES, which
sit at depth `> 0` — so the statement to prove is not "`red` fixes the region's matrices" but
the more informative one it needs as its induction hypothesis.  Measured over every index
with at most 4 nodes and levels below 3 whose non-top nodes obey the normal form (`nfFree`,
1047 of them), at every depth `d = 0, 1, 2, 3`:

    red (psM (matB s d))  =  (topSplit s).flatMap (fun q => psM (matB q (lvlB q)))

**and the right-hand side does not mention `d`.**  `red` re-roots every top-level subtree so
that its root's DEPTH equals its root's LEVEL — that is what "reduced" means, and it is why
`jjSeq 0 tr` (the diagonal `(0,0)(1,1)…(tr,tr)`) is the shape `red` cuts off the front.  On
the principal indices (344 of the 1047) it reads

    red (psM (matB (nd v nil a) d))  =  psM (matB (nd v nil a) v)

`nfB` is the case where every top-level level is `0`, so every summand is already re-rooted
at depth 0 and the right-hand side collapses to `psM (matB t 0)` — that is `canon_nfB` below,
and it is exactly the bridge from the measured identity to the gate `isReducedP`.

WHAT IS NOT CLAIMED.  The identity above is measured, not proved.  `Rows/Ladder.lean` carries
the matrix-independent branch lemmas it will be proved from (`red_jj`, `red_fold_open`,
`red_fold_single`, `red_shift`, `red_head_one`, `isPrincipalP_of_chain`, `trMax_eq`); that
file imports only `Trans.Recal`, so using it here is not a layering inversion. -/

section
open Trans.Recal

/-- 最上位の節の段は自由、それ以外は親 + 1 以下。`red` の再帰が降りる先の条件。 -/
def nfFree : B → Bool
  | .nil => true
  | .nd v r a => nfFree r && nfLe (v + 1) a

/-- 根の段。 -/
def lvlB : B → Nat
  | .nil => 0
  | .nd v _ _ => v

/-- `red` が返すはずの形: 各加数を「根の深さ = 根の段」の位置に置き直したもの。 -/
def canon (s : B) : PS := (topSplit s).flatMap fun q => psM (matB q (lvlB q))

theorem nfFree_of_nfLe : ∀ (t : B) (m : Nat), nfLe m t = true → nfFree t = true := by
  intro t
  induction t with
  | nil => intro _ _; rfl
  | nd v r a ihr _ =>
    intro m h
    obtain ⟨_, h2, h3⟩ := (nfLe_nd_iff m v r a).mp h
    show (nfFree r && nfLe (v + 1) a) = true
    rw [ihr m h2, h3]
    rfl

theorem lvlB_topSplit : ∀ (t : B), nfB t = true → ∀ q ∈ topSplit t, lvlB q = 0 := by
  intro t
  show nfLe 0 t = true → _
  induction t with
  | nil => intro _ q hq; exact absurd (show q ∈ ([] : List B) from hq) (by simp)
  | nd v r a ihr _ =>
    intro h q hq
    obtain ⟨h1, h2, _⟩ := (nfLe_nd_iff 0 v r a).mp h
    rcases List.mem_append.mp hq with hq | hq
    · exact ihr h2 q hq
    · rcases List.mem_cons.mp hq with rfl | hq
      · show v = 0; omega
      · exact absurd (show q ∈ ([] : List B) from hq) (by simp)

theorem psM_flatten : ∀ (X : List Matrix), psM X.flatten = (X.map psM).flatten := by
  intro X
  induction X with
  | nil => rfl
  | cons c cs ih =>
    show psM (c ++ cs.flatten) = psM c ++ (cs.map psM).flatten
    rw [psM_append, ih]

/-- **標準形なら `canon` は行列そのもの。** 測定した等式から門への橋。 -/
theorem canon_nfB (t : B) (h : nfB t = true) : canon t = psM (matB t 0) := by
  show ((topSplit t).map fun q => psM (matB q (lvlB q))).flatten = _
  rw [show ((topSplit t).map fun q => psM (matB q (lvlB q)))
      = ((topSplit t).map (fun q => matB q 0)).map psM from by
    rw [List.map_map]
    exact List.map_congr_left (fun q hq => by rw [lvlB_topSplit t h q hq]; rfl),
    ← psM_flatten, ← matB_topSplit t 0]

/-! ### §20.1 THE MEASUREMENT -/

def enumFree (L n : Nat) : List B :=
  ((List.range (n + 1)).flatMap (enumNodes L)).filter fun t => nfFree t && t != .nil

#guard (enumFree 3 4).length == 1047
#guard (List.range 4).all fun d =>
  (enumFree 3 4).all fun s => redP (psM (matB s d)) == canon s
#guard ((enumFree 3 4).filter fun s => match s with
  | .nd _ .nil _ => true | _ => false).length == 344
#guard (List.range 4).all fun d =>
  ((enumFree 3 4).filter fun s => match s with | .nd _ .nil _ => true | _ => false).all
    fun s => redP (psM (matB s d)) == psM (matB s (lvlB s))

end

/-! ## §21 THE `red` PROOF: THE MACHINERY, AND THE BASE CASE

§20 pinned the identity.  This section proves the base case of its induction and builds the
unfoldings the rest of it will run on.  `Rows/Ladder.lean` already opens `red`'s branches
matrix-independently (`red_jj`, `red_shift`, `red_fold_open`, `red_fold_single`) and turns a
row-0 parent chain into `isPrincipalP`/`isAnc`, and it imports only `Trans.Recal`; what was
missing is the same service for the two PARENT SEARCHES and for `red`'s remaining branch.

    fpar0Aux_hit / fpar1Aux_hit    one step of the leftward scan, when it hits
    fpar_oob / fpar0_in            the range guards
    isParentP_of_fpar / _of_ne     `isParentP` from the parent it found
    red_head_pos                   the branch `red` takes when the head's LEVEL is positive
                                   (`Rows/Ladder.lean` only had `gp1 = 0` and `gp1 = 1`)

**THE BASE CASE.**  A one-node index is one column, and `red` moves it to depth = level:

    red (f + 2) (psM (matB (nd v nil nil) d))  =  canon (nd v nil nil)  =  [(v, v)]

For `v = 0` that is `isZeroP`, one step.  For `v ≥ 1` it is the interesting branch and it
shows the whole mechanism in miniature: `red` prepends the diagonal `jjSeq 0 (v-1)`, pushes
the column out by `v`, reduces THAT (which is a diagonal with one deep column on the end, so
`trMax` runs to the end and `red_jj` collapses it to `jjSeq 0 v`), then drops the first `v`
columns and shifts back.  `diagT`/`red_diagT` is that middle matrix, isolated — it is the
shape every later branch reduces to, so it is written once here. -/

section
open Trans.Recal

/-! list plumbing -/

theorem getD_app_left {α : Type _} (L R : List α) (dd : α) (i : Nat) (h : i < L.length) :
    (L ++ R).getD i dd = L.getD i dd := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {α : Type _} (L R : List α) (dd : α) (i : Nat) (h : L.length ≤ i) :
    (L ++ R).getD i dd = R.getD (i - L.length) dd := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_map_range {α : Type _} (n : Nat) (f : Nat → α) (dd : α) : ∀ (i : Nat), i < n →
    ((List.range n).map f).getD i dd = f i := by
  intro i h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    show (List.range n)[i]? = some i from by simp [h]]
  rfl

/-! ### the diagonal -/

theorem jjSeq_zero (w : Nat) : jjSeq 0 ((w : Nat) : Int)
    = (List.range (w + 1)).map (fun (k : Nat) => (((k : Nat) : Int), ((k : Nat) : Int))) := by
  show (List.range (((w : Nat) : Int) - 0 + 1).toNat).map
    (fun (k : Nat) => ((0 : Int) + Int.ofNat k, (0 : Int) + Int.ofNat k)) = _
  rw [show (((w : Nat) : Int) - 0 + 1).toNat = w + 1 from by omega]
  exact List.map_congr_left (fun k _ => by
    show ((0 : Int) + Int.ofNat k, (0 : Int) + Int.ofNat k)
      = (((k : Nat) : Int), ((k : Nat) : Int))
    simp)

theorem jjSeq_length (w : Nat) : (jjSeq 0 ((w : Nat) : Int)).length = w + 1 := by
  rw [jjSeq_zero w, List.length_map, List.length_range]

theorem jjSeq_getD (w i : Nat) (h : i < w + 1) :
    (jjSeq 0 ((w : Nat) : Int)).getD i (0, 0) = (((i : Nat) : Int), ((i : Nat) : Int)) := by
  rw [jjSeq_zero w]
  exact getD_map_range (w + 1) _ (0, 0) i h

/-- 対角の後ろに深い列を 1 本足したもの。 -/
def diagT (w : Nat) (D : Int) : PS :=
  jjSeq 0 ((w : Nat) : Int) ++ [(D, ((w + 1 : Nat) : Int))]

theorem diagT_length (w : Nat) (D : Int) : (diagT w D).length = w + 2 := by
  show ((jjSeq 0 ((w : Nat) : Int)) ++ [(D, ((w + 1 : Nat) : Int))]).length = _
  rw [List.length_append, jjSeq_length w]
  rfl

theorem diagT_lenI (w : Nat) (D : Int) : lenI (diagT w D) = ((w + 2 : Nat) : Int) := by
  show (((diagT w D).length : Nat) : Int) = _
  rw [diagT_length]

theorem diagT_lo (w : Nat) (D : Int) (i : Nat) (h : i < w + 1) :
    gp0 (diagT w D) ((i : Nat) : Int) = ((i : Nat) : Int)
      ∧ gp1 (diagT w D) ((i : Nat) : Int) = ((i : Nat) : Int) := by
  have hg : (diagT w D).getD i (0, 0) = (((i : Nat) : Int), ((i : Nat) : Int)) := by
    show ((jjSeq 0 ((w : Nat) : Int)) ++ [(D, ((w + 1 : Nat) : Int))]).getD i (0, 0) = _
    rw [getD_app_left _ _ _ i (by rw [jjSeq_length w]; omega), jjSeq_getD w i h]
  constructor
  · show (if ((i : Nat) : Int) < 0 then (0 : Int)
          else ((diagT w D).getD ((i : Nat) : Int).toNat (0, 0)).1) = _
    rw [if_neg (by omega)]
    show ((diagT w D).getD i (0, 0)).1 = _
    rw [hg]
  · show (if ((i : Nat) : Int) < 0 then (0 : Int)
          else ((diagT w D).getD ((i : Nat) : Int).toNat (0, 0)).2) = _
    rw [if_neg (by omega)]
    show ((diagT w D).getD i (0, 0)).2 = _
    rw [hg]

theorem diagT_hi (w : Nat) (D : Int) :
    gp0 (diagT w D) ((w + 1 : Nat) : Int) = D
      ∧ gp1 (diagT w D) ((w + 1 : Nat) : Int) = ((w + 1 : Nat) : Int) := by
  have hg : (diagT w D).getD (w + 1) (0, 0) = (D, ((w + 1 : Nat) : Int)) := by
    show ((jjSeq 0 ((w : Nat) : Int)) ++ [(D, ((w + 1 : Nat) : Int))]).getD (w + 1) (0, 0) = _
    rw [getD_app_right _ _ _ (w + 1) (by rw [jjSeq_length w]; omega), jjSeq_length w,
      show w + 1 - (w + 1) = 0 from by omega]
    rfl
  constructor
  · show (if ((w + 1 : Nat) : Int) < 0 then (0 : Int)
          else ((diagT w D).getD ((w + 1 : Nat) : Int).toNat (0, 0)).1) = _
    rw [if_neg (by omega)]
    show ((diagT w D).getD (w + 1) (0, 0)).1 = _
    rw [hg]
  · show (if ((w + 1 : Nat) : Int) < 0 then (0 : Int)
          else ((diagT w D).getD ((w + 1 : Nat) : Int).toNat (0, 0)).2) = _
    rw [if_neg (by omega)]
    show ((diagT w D).getD (w + 1) (0, 0)).2 = _
    rw [hg]

/-! ### one-step unfoldings of the parent searches -/

theorem beqI_self (n : Int) : (n == n) = true := decide_eq_true rfl

theorem fpar0Aux_hit (f : Nat) (M : PS) (tgt j0 k : Int) (h1 : k ≤ j0) (h2 : gp0 M j0 < tgt) :
    fpar0Aux (f + 1) M tgt j0 k = j0 := by
  show (if j0 < k then (-1 : Int) else if gp0 M j0 < tgt then j0 else _) = _
  rw [if_neg (by omega), if_pos h2]

theorem fpar1Aux_hit (f : Nat) (M : PS) (tgt j0 k j1 : Int)
    (h0 : fpar0 M j0 k = j1) (h1 : k ≤ j1) (h2 : gp1 M j1 < tgt) :
    fpar1Aux (f + 1) M tgt j0 k = j1 := by
  show (let z := fpar0 M j0 k
        if z < k then (-1 : Int) else if gp1 M z < tgt then z else _) = _
  rw [h0, if_neg (by omega), if_pos h2]

theorem fpar_oob (M : PS) (i : Nat) (j k : Int) (h : j < 0 ∨ j ≥ lenI M) :
    fpar M i j k = -1 := by
  show (if j < 0 ∨ j ≥ lenI M then (-1 : Int) else _) = _
  rw [if_pos h]

theorem fpar0_in (M : PS) (j k : Int) (h : ¬(j < 0 ∨ j ≥ lenI M)) :
    fpar0 M j k = fpar0Aux (M.length + 1) M (gp0 M j) (j - 1) k := by
  show (if j < 0 ∨ j ≥ lenI M then (-1 : Int) else _) = _
  rw [if_neg h]

theorem isParentP_of_fpar (M : PS) (i : Nat) (j k : Int) (h0 : 0 ≤ k) (h1 : k < lenI M)
    (h2 : fpar M i j k = k) : isParentP M i j k = true := by
  show (decide (0 ≤ k) && decide (k < lenI M) && (k == fpar M i j k)) = true
  rw [h2, decide_eq_true h0, decide_eq_true h1, beqI_self]
  rfl

theorem isParentP_of_ne (M : PS) (i : Nat) (j k : Int) (h : (k == fpar M i j k) = false) :
    isParentP M i j k = false := by
  show (decide (0 ≤ k) && decide (k < lenI M) && (k == fpar M i j k)) = false
  rw [h, Bool.and_false]

/-! ### `red` on the diagonal-plus-one -/

theorem diagT_par (w : Nat) (D : Int) (hD : ((w : Nat) : Int) < D) (k : Nat)
    (hk1 : 1 ≤ k) (hk2 : k < w + 2) :
    fpar (diagT w D) 0 ((k : Nat) : Int) 0 = ((k - 1 : Nat) : Int) := by
  have hlt : gp0 (diagT w D) ((k - 1 : Nat) : Int) < gp0 (diagT w D) ((k : Nat) : Int) := by
    rcases Nat.lt_or_ge k (w + 1) with hkw | hkw
    · rw [(diagT_lo w D (k - 1) (by omega)).1, (diagT_lo w D k hkw).1]
      omega
    · have hkeq : k = w + 1 := by omega
      subst hkeq
      rw [(diagT_lo w D (w + 1 - 1) (by omega)).1, (diagT_hi w D).1]
      omega
  rw [fpar_zero, fpar0_in _ _ _ (by rw [diagT_lenI]; omega),
    show ((k : Nat) : Int) - 1 = ((k - 1 : Nat) : Int) from by omega,
    fpar0Aux_hit _ _ _ _ _ (by omega) hlt]

theorem diagT_par0 (w : Nat) (D : Int) : fpar (diagT w D) 0 ((0 : Nat) : Int) 0 = -1 := by
  rw [fpar_zero, fpar0_in _ _ _ (by rw [diagT_lenI]; omega)]
  exact fpar0Aux_neg _ _ _ _ _ (by omega)

theorem diagT_prin (w : Nat) (D : Int) (hD : ((w : Nat) : Int) < D) :
    isPrincipalP (diagT w D) = true := by
  refine Rows.Ladder.isPrincipalP_of_chain (M := diagT w D) (par := fun k => k - 1)
    (fun k h1 h2 => diagT_par w D hD k h1 (by rw [diagT_length] at h2; omega))
    (fun k h1 _ => by show k - 1 < k; omega) (diagT_par0 w D) (by rw [diagT_length]; omega)

theorem diagT_trMax (w : Nat) (D : Int) (hD : ((w : Nat) : Int) < D) :
    trMax (diagT w D) = lenI (diagT w D) - 1 := by
  rw [diagT_lenI, show ((w + 2 : Nat) : Int) - 1 = ((w + 1 : Nat) : Int) from by omega]
  refine Rows.Ladder.trMax_eq (diagT w D) (w + 1) (by rw [diagT_length]; omega) ?_ ?_
  · intro j hj
    refine isParentP_of_fpar _ _ _ _ (by omega) (by rw [diagT_lenI]; omega) ?_
    have hp0 : fpar0 (diagT w D) (((j : Nat) : Int) + 1) ((j : Nat) : Int)
        = ((j : Nat) : Int) := by
      have hlt : gp0 (diagT w D) ((j : Nat) : Int)
          < gp0 (diagT w D) ((j + 1 : Nat) : Int) := by
        rcases Nat.lt_or_ge (j + 1) (w + 1) with hjw | hjw
        · rw [(diagT_lo w D j (by omega)).1, (diagT_lo w D (j + 1) hjw).1]; omega
        · have : j + 1 = w + 1 := by omega
          rw [(diagT_lo w D j (by omega)).1, show ((j + 1 : Nat) : Int) = ((w + 1 : Nat) : Int)
            from by omega, (diagT_hi w D).1]
          omega
      rw [fpar0_in _ _ _ (by rw [diagT_lenI]; omega),
        show ((j : Nat) : Int) + 1 - 1 = ((j : Nat) : Int) from by omega,
        show ((j : Nat) : Int) + 1 = ((j + 1 : Nat) : Int) from by omega]
      exact fpar0Aux_hit _ _ _ _ _ (by omega) hlt
    have hlt1 : gp1 (diagT w D) ((j : Nat) : Int)
        < gp1 (diagT w D) (((j : Nat) : Int) + 1) := by
      rcases Nat.lt_or_ge (j + 1) (w + 1) with hjw | hjw
      · rw [(diagT_lo w D j (by omega)).2,
          show ((j : Nat) : Int) + 1 = ((j + 1 : Nat) : Int) from by omega,
          (diagT_lo w D (j + 1) hjw).2]
        omega
      · have : j + 1 = w + 1 := by omega
        rw [(diagT_lo w D j (by omega)).2,
          show ((j : Nat) : Int) + 1 = ((w + 1 : Nat) : Int) from by omega,
          (diagT_hi w D).2]
        omega
    rw [Rows.Ladder.fpar1_unfold _ _ _ (by rw [diagT_lenI]; omega)]
    exact fpar1Aux_hit _ _ _ _ _ _ hp0 (by omega) hlt1
  · refine isParentP_of_ne _ _ _ _ ?_
    rw [fpar_oob _ _ _ _ (by rw [diagT_lenI]; omega)]
    exact decide_eq_false (by omega)

/-- **対角に深い列を 1 本足した行列は、1 段長い対角に落ちる。** -/
theorem red_diagT (w : Nat) (D : Int) (hD : ((w : Nat) : Int) < D) (g : Nat) :
    red (g + 1) (diagT w D) = jjSeq 0 ((w + 1 : Nat) : Int) := by
  rw [Rows.Ladder.red_jj (diagT w D) g ?hz (diagT_prin w D hD) ?h0 ?h1 (diagT_trMax w D hD),
    diagT_lenI, show ((w + 2 : Nat) : Int) - 1 = ((w + 1 : Nat) : Int) from by omega]
  case hz =>
    show ((diagT w D).length == 1 && (gp1 (diagT w D) 0 == 0)) = false
    rw [show ((diagT w D).length == 1) = false from by rw [diagT_length]; simp]
    rfl
  case h0 => exact (diagT_lo w D 0 (by omega)).1
  case h1 => exact (diagT_lo w D 0 (by omega)).2

/-! ### the single-node case -/

theorem jjSeq_lenI (w : Nat) : lenI (jjSeq 0 ((w : Nat) : Int)) = ((w + 1 : Nat) : Int) := by
  show (((jjSeq 0 ((w : Nat) : Int)).length : Nat) : Int) = _
  rw [jjSeq_length]

theorem jjSeq_gp (w i : Nat) (h : i < w + 1) :
    gp0 (jjSeq 0 ((w : Nat) : Int)) ((i : Nat) : Int) = ((i : Nat) : Int)
      ∧ gp1 (jjSeq 0 ((w : Nat) : Int)) ((i : Nat) : Int) = ((i : Nat) : Int) := by
  constructor
  · show (if ((i : Nat) : Int) < 0 then (0 : Int)
          else ((jjSeq 0 ((w : Nat) : Int)).getD ((i : Nat) : Int).toNat (0, 0)).1) = _
    rw [if_neg (by omega)]
    show ((jjSeq 0 ((w : Nat) : Int)).getD i (0, 0)).1 = _
    rw [jjSeq_getD w i h]
  · show (if ((i : Nat) : Int) < 0 then (0 : Int)
          else ((jjSeq 0 ((w : Nat) : Int)).getD ((i : Nat) : Int).toNat (0, 0)).2) = _
    rw [if_neg (by omega)]
    show ((jjSeq 0 ((w : Nat) : Int)).getD i (0, 0)).2 = _
    rw [jjSeq_getD w i h]

theorem drop_app_len {α : Type _} (L R : List α) (n : Nat) (h : L.length = n) :
    (L ++ R).drop n = R := by
  subst h; exact List.drop_left

theorem jjSeq_drop_last (w : Nat) :
    (jjSeq 0 ((w + 1 : Nat) : Int)).drop (w + 1)
      = [(((w + 1 : Nat) : Int), ((w + 1 : Nat) : Int))] := by
  rw [jjSeq_zero (w + 1), List.range_succ, List.map_append,
    drop_app_len _ _ (w + 1) (by simp)]
  rfl

theorem red_head_pos (M : PS) (f : Nat) (hzero : isZeroP M = false)
    (hprin : isPrincipalP M = true) (hg1 : (gp1 M 0 == 0) = false) :
    red (f + 1) M
      = (let N := red f (jjSeq 0 (gp1 M 0 - 1) ++ incrFirst M (gp1 M 0))
         let jN : Int := lenI N - 1
         if decide (gp1 M 0 ≤ jN) && isPrincipalP (N.drop (gp1 M 0).toNat) then
           incrFirst (N.drop (gp1 M 0).toNat) (-(gp0 N (gp1 M 0)) + gp1 N (gp1 M 0))
         else M) := by
  simp only [Trans.Recal.red]
  rw [hzero]
  simp only [Bool.false_eq_true, if_false]
  rw [hprin]
  simp only [if_true]
  rw [hg1]
  simp only [Bool.and_false, Bool.false_eq_true, if_false]

/-- **1 節の添字。** `red` はそれを「深さ = 段」の位置に置く。 -/
theorem red_leaf (d f : Nat) : ∀ v : Nat,
    red (f + 2) [(((d : Nat) : Int), ((v : Nat) : Int))]
      = [(((v : Nat) : Int), ((v : Nat) : Int))] := by
  intro v
  cases v with
  | zero =>
    simp only [Trans.Recal.red]
    rw [show isZeroP [(((d : Nat) : Int), ((0 : Nat) : Int))] = true from rfl]
    simp only [if_true]
    rfl
  | succ w =>
    have hg1M : gp1 [(((d : Nat) : Int), ((w + 1 : Nat) : Int))] 0
        = ((w + 1 : Nat) : Int) := rfl
    have hzero : isZeroP [(((d : Nat) : Int), ((w + 1 : Nat) : Int))] = false := by
      show ([(((d : Nat) : Int), ((w + 1 : Nat) : Int))].length == 1
        && (gp1 [(((d : Nat) : Int), ((w + 1 : Nat) : Int))] 0 == 0)) = false
      rw [hg1M, show (((w + 1 : Nat) : Int) == 0) = false from decide_eq_false (by omega)]
      rfl
    have hprin : isPrincipalP [(((d : Nat) : Int), ((w + 1 : Nat) : Int))] = true :=
      Rows.Ladder.isPrincipalP_single _ _ (decide_eq_false (by omega))
    have hne : (gp1 [(((d : Nat) : Int), ((w + 1 : Nat) : Int))] 0 == 0) = false := by
      rw [hg1M]; exact decide_eq_false (by omega)
    have harg : jjSeq 0 (((w + 1 : Nat) : Int) - 1)
        ++ incrFirst [(((d : Nat) : Int), ((w + 1 : Nat) : Int))] ((w + 1 : Nat) : Int)
        = diagT w (((d : Nat) : Int) + ((w + 1 : Nat) : Int)) := by
      rw [show ((w + 1 : Nat) : Int) - 1 = ((w : Nat) : Int) from by omega]
      rfl
    have hred : red (f + 1) (jjSeq 0 (((w + 1 : Nat) : Int) - 1)
        ++ incrFirst [(((d : Nat) : Int), ((w + 1 : Nat) : Int))] ((w + 1 : Nat) : Int))
        = jjSeq 0 ((w + 1 : Nat) : Int) := by
      rw [harg]
      exact red_diagT w _ (by omega) f
    rw [red_head_pos _ (f + 1) hzero hprin hne, hg1M, hred]
    show (if decide (((w + 1 : Nat) : Int) ≤ lenI (jjSeq 0 ((w + 1 : Nat) : Int)) - 1)
            && isPrincipalP ((jjSeq 0 ((w + 1 : Nat) : Int)).drop ((w + 1 : Nat) : Int).toNat)
          then incrFirst ((jjSeq 0 ((w + 1 : Nat) : Int)).drop ((w + 1 : Nat) : Int).toNat)
                 (-(gp0 (jjSeq 0 ((w + 1 : Nat) : Int)) ((w + 1 : Nat) : Int))
                   + gp1 (jjSeq 0 ((w + 1 : Nat) : Int)) ((w + 1 : Nat) : Int))
          else [(((d : Nat) : Int), ((w + 1 : Nat) : Int))]) = _
    rw [show ((w + 1 : Nat) : Int).toNat = w + 1 from rfl, jjSeq_drop_last w, jjSeq_lenI,
      (jjSeq_gp (w + 1) (w + 1) (by omega)).1, (jjSeq_gp (w + 1) (w + 1) (by omega)).2,
      decide_eq_true (show ((w + 1 : Nat) : Int) ≤ ((w + 1 + 1 : Nat) : Int) - 1 from by omega),
      Rows.Ladder.isPrincipalP_single _ _ (show (((w + 1 : Nat) : Int) == 0) = false from
        decide_eq_false (by omega))]
    simp only [Bool.and_self, if_true]
    show [(((w + 1 : Nat) : Int)
      + (-((w + 1 : Nat) : Int) + ((w + 1 : Nat) : Int)), ((w + 1 : Nat) : Int))] = _
    rw [show ((w + 1 : Nat) : Int) + (-((w + 1 : Nat) : Int) + ((w + 1 : Nat) : Int))
      = ((w + 1 : Nat) : Int) from by omega]

/-- §20 の等式の基底: 節が 1 つの添字。 -/
theorem red_canon_leaf (v d f : Nat) :
    red (f + 2) (psM (matB (.nd v .nil .nil) d)) = canon (.nd v .nil .nil) := by
  show red (f + 2) [(((d : Nat) : Int), ((v : Nat) : Int))] = _
  rw [red_leaf d f v]
  rfl

end

/-! ## §22 THE `red` PROOF: SUMS, THE DEPTH SHIFT, AND WHAT IS LEFT

§21 did the base case.  Three more of §20's cases fall out of what is already proved, and
after them exactly ONE is left.

**`isAnc` at row 0 is "the parent chain reaches column 0".**  `isAncAux` follows `fpar`, which
§18.1 identifies with `BMS.parent`, and §8 says the chain is the left-minima — so

    isAncAux … j … = true   ↔   j = 0  ∨  every column in (0, j] is deeper than column 0

(`isAncAux_imp` and `isAncAux_of_lmin`, the two directions).  Both branch conditions of `red`
follow at once: a `matB` matrix with two or more top-level summands is NOT principal (the
second summand's root is at depth 0 again, so column 0 is not a left-minimum of the last
column), and one with a single root IS principal (everything after the root is deeper).

**SUMS.**  `red` then takes the `ppair` branch, and §18.3 already says `ppair` is the
top-level split, so the whole case is the induction hypothesis applied summand by summand:

    red_canon_sum : (∀ q ∈ topSplit s, red f (psM (matB q 0)) = canon q)
                    → red (f+1) (psM (matB s 0)) = canon s

**THE DEPTH SHIFT.**  A single root of level 0 sitting at depth `d > 0` has `gp1 = 0`, so
`red` takes `Rows/Ladder.lean`'s `red_shift` branch and slides the whole matrix back to depth
0 — which is `matB` at depth 0, because `matB t d = sh d (matB t 0)` (§4) and `psM` turns `sh`
into `incrFirst`:

    red_canon_shift : red (f+1) (psM (matB (nd 0 nil a) d)) = red f (psM (matB (nd 0 nil a) 0))

**WHAT IS LEFT IS ONE CASE: THE FOLD.**  A principal index whose root has level 0 at depth 0
is the branch that cuts off the diagonal `jjSeq 0 (trMax M)` and folds over `brF M`.  The
`v ≥ 1` case reduces to it as well (`red_head_pos` prepends a diagonal and pushes the tree
out).  What that case needs, and what the measurements of §20 say, is:

  * the initial run `0 … trMax M` is the tree's LEFTMOST PATH WITH LEVELS `0, 1, 2, …` — under
    `nfFree` a child's level exceeds its parent's by at most one, so `isParentP … 1` at row 1
    forces equality, and the run is literally `jjSeq 0 tr`;
  * the branches `brF M` are the maximal subtrees hanging off that spine, so their joints are
    spine columns, where INDEX = LEVEL;
  * hence a branch root of level `u` has its row-1 parent at spine index `u - 1`, which is why
    `red`'s reconstruction `(jnJ + 1, nJ + 1) :: derp bJ` puts back the level it removed. -/

section
open Trans.Recal

/-! ### `isAnc` at row 0 is reaching column 0 along the parent chain -/

theorem isAncAux_imp : ∀ (f : Nat) (M : Matrix) (j : Nat), j < M.length →
    isAncAux f (psM M) 0 ((j : Nat) : Int) 0 = true → (j = 0 ∨ LMin M 0 j) := by
  intro f
  induction f with
  | zero => intro M j _ h; exact absurd h (by simp [isAncAux])
  | succ g ih =>
    intro M j hj h
    by_cases hj0 : j = 0
    · exact Or.inl hj0
    have hstep : isAncAux (g + 1) (psM M) 0 ((j : Nat) : Int) 0
        = (if (0 : Int) == ((j : Nat) : Int) then true
           else if fpar (psM M) 0 ((j : Nat) : Int) 0 == -1 then false
           else isAncAux g (psM M) 0 (fpar (psM M) 0 ((j : Nat) : Int) 0) 0) := rfl
    rw [hstep, if_neg (by
      intro hc
      have hcc : (0 : Int) = ((j : Nat) : Int) := of_decide_eq_true hc
      exact hj0 (by omega))] at h
    rw [fpar_zero, fpar0_eq_parent M j hj] at h
    cases hp : parent M 0 j with
    | none =>
      rw [hp] at h
      exact absurd h (by simp)
    | some q =>
      rw [hp] at h
      have hqj : q < j := by
        obtain ⟨hrm, _⟩ := List.max?_eq_some_iff.mp hp
        exact List.mem_range.mp (List.mem_filter.mp hrm).1
      have hlmq : LMin M q j := by
        refine lmin_of_fpar0 M j q hj ?_
        rw [fpar0_eq_parent M j hj, hp]
      rw [show (((q : Nat) : Int) == -1) = false from decide_eq_false (by omega),
        if_neg (by simp)] at h
      rcases ih M q (by omega) h with rfl | hlm0
      · exact Or.inr hlmq
      · refine Or.inr ⟨by omega, ?_⟩
        intro p hp1 hp2
        rcases Nat.lt_or_ge p (q + 1) with hpq | hpq
        · exact hlm0.2 p hp1 (by omega)
        · exact Nat.lt_trans (hlm0.2 q hlm0.1 (Nat.le_refl q)) (hlmq.2 p (by omega) hp2)

theorem isAnc_false_of_flat (M : Matrix) (b : Nat) (hb : 0 < b) (hlen : 1 < M.length)
    (hble : b < M.length) (he : ent M b 0 ≤ ent M 0 0) :
    isAnc (psM M) 0 (lenI (psM M) - 1) 0 = false := by
  have hlenI : lenI (psM M) - 1 = ((M.length - 1 : Nat) : Int) := by
    show (((psM M).length : Nat) : Int) - 1 = _
    rw [psM_len]; omega
  cases hres : isAnc (psM M) 0 (lenI (psM M) - 1) 0 with
  | false => rfl
  | true =>
    exfalso
    rw [hlenI] at hres
    have hin : isAncAux ((psM M).length + 1) (psM M) 0 ((M.length - 1 : Nat) : Int) 0 = true := by
      have : isAnc (psM M) 0 ((M.length - 1 : Nat) : Int) 0
          = (if (0 : Int) < 0 ∨ (0 : Int) ≥ lenI (psM M) then false
             else isAncAux ((psM M).length + 1) (psM M) 0 ((M.length - 1 : Nat) : Int) 0) := rfl
      rw [this, if_neg (by
        show ¬((0 : Int) < 0 ∨ (0 : Int) ≥ (((psM M).length : Nat) : Int))
        rw [psM_len]; omega)] at hres
      exact hres
    rcases isAncAux_imp _ M (M.length - 1) (by omega) hin with hz | hlm
    · omega
    · exact absurd (hlm.2 b hb (by omega)) (by omega)

/-! ### the non-principal branch -/

theorem red_nonprin (M : PS) (f : Nat) (hzero : isZeroP M = false)
    (hprin : isPrincipalP M = false) : red (f + 1) M = (ppair M).flatMap (red f) := by
  simp only [Trans.Recal.red]
  rw [hzero]
  simp only [Bool.false_eq_true, if_false]
  rw [hprin]
  simp only [Bool.false_eq_true, if_false]

theorem matB_ne_nil_len (t : B) (h : t ≠ .nil) : 0 < (matB t 0).length := matB_len_pos t 0 h

/-- 最上位の加数が 2 つ以上なら principal ではない。 -/
theorem not_prin_sum (v : Nat) (r a : B) (hr : r ≠ .nil) :
    isPrincipalP (psM (matB (.nd v r a) 0)) = false := by
  have hM : matB (.nd v r a) 0 = matB r 0 ++ matB (.nd v .nil a) 0 := rfl
  have hrlen : 0 < (matB r 0).length := matB_ne_nil_len r hr
  have hblen : 0 < (matB (.nd v .nil a) 0).length :=
    matB_ne_nil_len _ (by intro h; exact B.noConfusion h)
  have hlen : (matB (.nd v r a) 0).length = (matB r 0).length + (matB (.nd v .nil a) 0).length := by
    rw [hM, List.length_append]
  have hent0 : ent (matB (.nd v r a) 0) 0 0 = ent (matB r 0) 0 0 := by
    rw [hM]; exact ent_append_left _ _ 0 0 hrlen
  have hentb : ent (matB (.nd v r a) 0) (matB r 0).length 0 = 0 := by
    rw [hM, ent_append _ _ _ 0 (Nat.le_refl _),
      show (matB r 0).length - (matB r 0).length = 0 from by omega]
    rfl
  show (!isZeroP (psM (matB (.nd v r a) 0))
    && isAnc (psM (matB (.nd v r a) 0)) 0 (lenI (psM (matB (.nd v r a) 0)) - 1) 0) = false
  rw [isAnc_false_of_flat _ (matB r 0).length hrlen (by omega) (by omega) (by
    rw [hentb, hent0]
    omega)]
  exact Bool.and_false _

theorem isZeroP_sum (v : Nat) (r a : B) (hr : r ≠ .nil) :
    isZeroP (psM (matB (.nd v r a) 0)) = false := by
  have hrlen : 0 < (matB r 0).length := matB_ne_nil_len r hr
  have hblen : 0 < (matB (.nd v .nil a) 0).length :=
    matB_ne_nil_len _ (by intro h; exact B.noConfusion h)
  have hlen : (matB (.nd v r a) 0).length = (matB r 0).length + (matB (.nd v .nil a) 0).length := by
    show (matB r 0 ++ matB (.nd v .nil a) 0).length = _
    rw [List.length_append]
  show ((psM (matB (.nd v r a) 0)).length == 1 && _) = false
  rw [show ((psM (matB (.nd v r a) 0)).length == 1) = false from by
    rw [psM_len]; exact decide_eq_false (by omega)]
  rfl

theorem topSplit_canon : ∀ (t : B), ∀ q ∈ topSplit t, canon q = psM (matB q (lvlB q)) := by
  intro t
  induction t with
  | nil => intro q h; exact absurd (show q ∈ ([] : List B) from h) (by simp)
  | nd v r a ihr _ =>
    intro q h
    rcases List.mem_append.mp h with h | h
    · exact ihr q h
    · rcases List.mem_cons.mp h with rfl | h
      · show ((topSplit (B.nd v .nil a)).map fun z => psM (matB z (lvlB z))).flatten = _
        show ([psM (matB (B.nd v .nil a) v)]).flatten = _
        rw [List.flatten_cons, List.flatten_nil, List.append_nil]
        rfl
      · exact absurd (show q ∈ ([] : List B) from h) (by simp)

/-- §20 の等式、最上位の加数が 2 つ以上の場合。 -/
theorem red_canon_sum (v : Nat) (r a : B) (hr : r ≠ .nil) (f : Nat)
    (ih : ∀ q ∈ topSplit (.nd v r a), red f (psM (matB q 0)) = canon q) :
    red (f + 1) (psM (matB (.nd v r a) 0)) = canon (.nd v r a) := by
  rw [red_nonprin _ f (isZeroP_sum v r a hr) (not_prin_sum v r a hr), ppair_matB,
    List.flatMap_map]
  show ((topSplit (.nd v r a)).map (fun q => red f (psM (matB q 0)))).flatten = _
  rw [List.map_congr_left (fun q hq =>
    (ih q hq).trans (topSplit_canon (.nd v r a) q hq))]
  rfl

/-! ### the depth shift -/

theorem isAncAux_of_lmin : ∀ (f : Nat) (M : Matrix) (j : Nat), j < f → j < M.length →
    (j = 0 ∨ LMin M 0 j) → isAncAux f (psM M) 0 ((j : Nat) : Int) 0 = true := by
  intro f
  induction f with
  | zero => intro M j h _ _; exact absurd h (by omega)
  | succ g ih =>
    intro M j hf hj hor
    have hstep : isAncAux (g + 1) (psM M) 0 ((j : Nat) : Int) 0
        = (if (0 : Int) == ((j : Nat) : Int) then true
           else if fpar (psM M) 0 ((j : Nat) : Int) 0 == -1 then false
           else isAncAux g (psM M) 0 (fpar (psM M) 0 ((j : Nat) : Int) 0) 0) := rfl
    rcases hor with rfl | hlm
    · rw [hstep, if_pos (show ((0 : Int) == ((0 : Nat) : Int)) = true from rfl)]
    · have hj0 : 0 < j := hlm.1
      have hmem : 0 ∈ (List.range j).filter (fun p => decide (ent M p 0 < ent M j 0)) :=
        List.mem_filter.mpr ⟨List.mem_range.mpr hj0,
          decide_eq_true (hlm.2 j hj0 (Nat.le_refl j))⟩
      cases hp : parent M 0 j with
      | none =>
        exfalso
        have := List.max?_eq_none_iff.mp hp
        rw [this] at hmem
        exact absurd hmem (by simp)
      | some q =>
        have hqj : q < j := by
          obtain ⟨hrm, _⟩ := List.max?_eq_some_iff.mp hp
          exact List.mem_range.mp (List.mem_filter.mp hrm).1
        rw [hstep, if_neg (by
          intro hc
          have hcc : (0 : Int) = ((j : Nat) : Int) := of_decide_eq_true hc
          omega), fpar_zero, fpar0_eq_parent M j hj, hp,
          show (((q : Nat) : Int) == -1) = false from decide_eq_false (by omega),
          if_neg (by simp)]
        refine ih M q (by omega) (by omega) ?_
        rcases Nat.eq_or_lt_of_le (Nat.zero_le q) with hq0 | hq0
        · exact Or.inl hq0.symm
        · exact Or.inr ⟨hq0, fun p hp1 hp2 => hlm.2 p hp1 (by omega)⟩

theorem prin_of_deep (M : Matrix) (hlen : 1 < M.length)
    (hdeep : ∀ p, 0 < p → p < M.length → ent M 0 0 < ent M p 0) :
    isPrincipalP (psM M) = true := by
  have hlenI : lenI (psM M) - 1 = ((M.length - 1 : Nat) : Int) := by
    show (((psM M).length : Nat) : Int) - 1 = _
    rw [psM_len]; omega
  show (!isZeroP (psM M) && isAnc (psM M) 0 (lenI (psM M) - 1) 0) = true
  rw [show isZeroP (psM M) = false from by
      show ((psM M).length == 1 && _) = false
      rw [show ((psM M).length == 1) = false from by
        rw [psM_len]; exact decide_eq_false (by omega)]
      rfl,
    hlenI,
    show isAnc (psM M) 0 ((M.length - 1 : Nat) : Int) 0 = true from by
      show (if (0 : Int) < 0 ∨ (0 : Int) ≥ lenI (psM M) then false
            else isAncAux ((psM M).length + 1) (psM M) 0 ((M.length - 1 : Nat) : Int) 0) = true
      rw [if_neg (by
        show ¬((0 : Int) < 0 ∨ (0 : Int) ≥ (((psM M).length : Nat) : Int))
        rw [psM_len]; omega)]
      refine isAncAux_of_lmin _ M (M.length - 1) (by rw [psM_len]; omega) (by omega) ?_
      exact Or.inr ⟨by omega, fun p hp1 hp2 => hdeep p hp1 (by omega)⟩]
  rfl

theorem matB_node_deep (v : Nat) (a : B) (d : Nat) : ∀ p, 0 < p →
    p < (matB (.nd v .nil a) d).length →
    ent (matB (.nd v .nil a) d) 0 0 < ent (matB (.nd v .nil a) d) p 0 := by
  intro p hp hlen
  obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
  have hlen2 : (matB (.nd v .nil a) d).length = (matB a (d + 1)).length + 1 := by
    show ([d, v] :: matB a (d + 1)).length = _
    simp
  have hi : i < (matB a (d + 1)).length := by omega
  have hlb := matB_col_lb a (d + 1) _ (getD_mem (matB a (d + 1)) [] i hi)
  show d < ((matB a (d + 1)).getD i []).getD 0 0
  omega

theorem getD_drop_one : ∀ (c : List Nat), (c.drop 1).getD 0 0 = c.getD 1 0
  | [] => rfl
  | _ :: _ => rfl

theorem psM_sh (e : Nat) (X : Matrix) : psM (sh e X) = incrFirst (psM X) ((e : Nat) : Int) := by
  show (X.map (shc e)).map _ = (X.map _).map _
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun c _ => ?_)
  show ((((shc e c).getD 0 0 : Nat) : Int), (((shc e c).getD 1 0 : Nat) : Int))
    = ((((c.getD 0 0 : Nat) : Int) + ((e : Nat) : Int)), (((c.getD 1 0 : Nat) : Int)))
  rw [show (shc e c).getD 0 0 = c.getD 0 0 + e from rfl,
    show (shc e c).getD 1 0 = c.getD 1 0 from getD_drop_one c,
    show (((c.getD 0 0 + e : Nat)) : Int) = (((c.getD 0 0 : Nat)) : Int) + ((e : Nat) : Int)
      from by omega]

theorem incrFirst_cancel : ∀ (Y : PS) (i : Int), incrFirst (incrFirst Y i) (-i) = Y := by
  intro Y
  induction Y with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro i
    show ((c.1 + i) + -i, c.2) :: incrFirst (incrFirst cs i) (-i) = c :: cs
    rw [ih i, show (c.1 + i) + -i = c.1 from by omega]

theorem matB_depth (t : B) (d : Nat) : matB t d = sh d (matB t 0) := by
  have h := matB_sh t 0 d
  rw [show 0 + d = d from by omega] at h
  exact h

/-- §20 の等式、principal かつ根の段 0 で深さ `d > 0` の場合: 深さ 0 へ落ちる。 -/
theorem red_canon_shift (a : B) (d f : Nat) (hd : 0 < d) (ha : a ≠ .nil) :
    red (f + 1) (psM (matB (.nd 0 .nil a) d)) = red f (psM (matB (.nd 0 .nil a) 0)) := by
  have hlen : 1 < (matB (.nd 0 .nil a) d).length := by
    have := matB_len_pos a (d + 1) ha
    show 1 < ([d, 0] :: matB a (d + 1)).length
    simp
    omega
  have hg0 : gp0 (psM (matB (.nd 0 .nil a) d)) 0 = ((d : Nat) : Int) := by
    show (if (0 : Int) < 0 then (0 : Int)
          else ((psM (matB (.nd 0 .nil a) d)).getD (0 : Int).toNat (0, 0)).1) = _
    rw [if_neg (by omega)]
    show ((psM (matB (.nd 0 .nil a) d)).getD 0 (0, 0)).1 = _
    rw [getD_psM]
    rfl
  have hg1 : gp1 (psM (matB (.nd 0 .nil a) d)) 0 = 0 := by
    show (if (0 : Int) < 0 then (0 : Int)
          else ((psM (matB (.nd 0 .nil a) d)).getD (0 : Int).toNat (0, 0)).2) = _
    rw [if_neg (by omega)]
    show ((psM (matB (.nd 0 .nil a) d)).getD 0 (0, 0)).2 = _
    rw [getD_psM]
    rfl
  rw [Rows.Ladder.red_shift _ f
    (by
      show ((psM (matB (.nd 0 .nil a) d)).length == 1 && _) = false
      rw [show ((psM (matB (.nd 0 .nil a) d)).length == 1) = false from by
        rw [psM_len]; exact decide_eq_false (by omega)]
      rfl)
    (prin_of_deep _ hlen (matB_node_deep 0 a d))
    (by rw [hg0]; exact decide_eq_false (by omega)) hg1, hg0,
    matB_depth (.nd 0 .nil a) d, psM_sh, incrFirst_cancel]

/-- §20 の等式、空の添字。 -/
theorem red_canon_nil (d : Nat) : ∀ (f : Nat), red f (psM (matB .nil d)) = canon .nil := by
  intro f
  cases f with
  | zero => rfl
  | succ g =>
    show red (g + 1) ([] : PS) = _
    rw [red_nonprin [] g (by decide) (by decide),
      show ppair ([] : PS) = [] from by decide]
    rfl

end

/-! ## §23 THE FOLD, PINNED

One case of §20 is left: a principal index whose root has level 0 at depth 0.  `red` cuts
`jjSeq 0 (trMax M)` off the front and folds over `brF M`, rebuilding each branch as
`(jnJ + 1, nJ + 1) :: derp bJ` and shifting the result by `jnJ - nJ`.  Four predictions,
measured over the indices with at most 4 (resp. 5) nodes and levels below 3 (resp. 4) that
obey the normal form off the top and are principal with root level 0 — 65 and 467 of them:

    trMax M       = the LEFTMOST PATH whose levels go 0, 1, 2, …   65 / 65
    (brF M).length = the maximal subtrees hanging off that path    65 / 65
    (jnJ+1, nJ+1) :: derp bJ  =  bJ                              467 / 467
    jnJ - nJ      = (branch root's depth) − (branch root's level) 467 / 467

**THE THIRD ONE IS THE CRUX AND IT IS AN IDENTITY: the rebuild gives the branch back.**  It
says two things at once — the joint is the branch root's tree parent (`jnJ + 1` is its depth)
and the row-1 parent's INDEX is the branch root's level minus one.  The second holds because
the joint lies on the diagonal spine, where index = level, and the normal form caps a child's
level at its parent's plus one; so the nearest ancestor of strictly smaller level is spine
column `u - 1`.

With it the fold collapses.  Each term is `incrFirst (red f bJ) (jnJ - nJ)`, the induction
hypothesis turns `red f bJ` into the branch re-rooted at its own level, and the fourth
prediction says the shift puts it back exactly where it was — so the fold reproduces
`M.drop (trMax M + 1)` and the diagonal reproduces `M.take (trMax M + 1)`.

What the proof still needs is the block decomposition of that suffix, which is §18.3's
`ppairAux_blocks` at arbitrary depth: the branch roots have NON-INCREASING depths as one
walks right (down the spine's children first, then back up), which is what makes each of them
a `ppair` cut. -/

section
open Trans.Recal

/-- 対角の長さの予測: 左端の道で段が 1 ずつ上がる長さ。 -/
partial def spineLen : B → Nat
  | .nd u .nil b =>
    match (topSplit b).head? with
    | none => 0
    | some q => if lvlB q == u + 1 then 1 + spineLen q else 0
  | _ => 0

/-- 枝の予測: 対角からぶら下がる極大部分木。 -/
partial def branchesOf : B → List B
  | .nd u .nil b =>
    (match topSplit b with
     | [] => []
     | q :: rest => if lvlB q == u + 1 then branchesOf q ++ rest else (q :: rest))
  | _ => []

/-- 段 0 で principal、引数が空でない添字。 -/
def enumPrin (L n : Nat) : List B := (enumFree L n).filter fun s => match s with
  | .nd 0 .nil (.nd _ _ _) => true | _ => false

/-- 枝の作り直しは枝そのものか。 -/
def rebuildOK (s : B) : Bool :=
  let M := psM (matB s 0)
  let br := brF M
  let fn := firstNodes M
  let jn := joints M
  (List.range br.length).all fun J =>
    let bJ := br.getD J []
    let nJ : Int := if gp1 bJ 0 == 0 then -1 else fpar M 1 (fn.getD J 0) 0
    let jnJ := jn.getD J 0
    ((jnJ + 1, nJ + 1) :: derp bJ) == bJ

/-- ずらし量は「枝の根の深さ − 枝の根の段」か。 -/
def shiftOK (s : B) : Bool :=
  let M := psM (matB s 0)
  let br := brF M
  let fn := firstNodes M
  let jn := joints M
  (List.range br.length).all fun J =>
    let bJ := br.getD J []
    let nJ : Int := if gp1 bJ 0 == 0 then -1 else fpar M 1 (fn.getD J 0) 0
    let jnJ := jn.getD J 0
    (jnJ - nJ) == gp0 bJ 0 - gp1 bJ 0

#guard (enumPrin 3 4).length == 65
#guard (enumPrin 3 4).all fun s => trMax (psM (matB s 0)) == ((spineLen s : Nat) : Int)
#guard (enumPrin 3 4).all fun s => (brF (psM (matB s 0))).length == (branchesOf s).length
#guard (enumPrin 4 5).length == 467
#guard (enumPrin 4 5).all rebuildOK
#guard (enumPrin 4 5).all shiftOK

end

/-! ## §24 `ppair` AT ARBITRARY DEPTH

§18.3 proved `ppair` is the block decomposition when every block's root sits at depth 0.
The fold needs it one level down: the suffix `M.drop (trMax M + 1)` is a run of subtrees
whose roots sit at the depths of the spine's children, and those depths DECREASE as one
walks right — first the deepest spine node's children, then back up.  So the hypothesis
"every root is at depth 0" becomes "every block's root is no deeper than any column before
it", which is exactly what makes `parent … = none` there and hence what makes `ppairAux`
cut at that column.

Everything else in the §18.3 proof was already about depths rather than about zero, so
generalising it took only replacing `ent … = 0` by `parent … = none` in `iterParent0_last`,
`fAnc_last` and `fAnc_last_self` (done in place — `parent0_none_of_zero` supplies the old
form at the old call sites) and adding `parent0_none_of_min`. -/

section
open Trans.Recal

theorem take_app_left {α : Type _} : ∀ (L R : List α) (n : Nat), n ≤ L.length →
    (L ++ R).take n = L.take n := by
  intro L
  induction L with
  | nil => intro R n h; rw [show n = 0 from by simp at h; omega]; rfl
  | cons x xs ih =>
    intro R n h
    cases n with
    | zero => rfl
    | succ k =>
      show x :: (xs ++ R).take k = x :: xs.take k
      rw [ih R k (by simp at h; omega)]

/-- 深さを問わないブロック: 先頭の列が同じブロックの他のどの列よりも浅い。 -/
def BlkG (Bk : Matrix) : Prop :=
  0 < Bk.length ∧ ∀ p, 0 < p → p < Bk.length → ent Bk 0 0 < ent Bk p 0

/-- **`ppair` はブロックの並びをそのまま返す (深さは任意)。**
    第 2 の仮定は「各ブロックの根は、それより前のどの列よりも浅くない」。 -/
theorem ppairAux_blocksG : ∀ (f : Nat) (Bs : List Matrix) (P : Matrix) (acc : List PS),
    (∀ Bk ∈ Bs, BlkG Bk) →
    (∀ k, k < Bs.length → ∀ i, i < ((Bs.take k).flatten).length →
      ent (Bs.getD k []) 0 0 ≤ ent ((Bs.take k).flatten) i 0) →
    Bs.length ≤ f →
    ppairAux f (psM (Bs.flatten ++ P)) ((Bs.flatten.length : Int) - 1) acc
      = Bs.map psM ++ acc := by
  intro f
  induction f with
  | zero =>
    intro Bs P acc _ _ hlen
    have : Bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ g ih =>
    intro Bs P acc hb hmin hlen
    rcases List.eq_nil_or_concat Bs with rfl | ⟨Bs', Bk, hcon⟩
    · show (if ((([] : List Matrix).flatten.length : Int) - 1) < 0 then acc else _) = _
      rw [if_pos (by simp)]
      rfl
    · rw [show Bs = Bs' ++ [Bk] from by rw [hcon, List.concat_eq_append]] at hb hmin hlen ⊢
      have hBk : BlkG Bk := hb Bk (by simp)
      have hb' : ∀ X ∈ Bs', BlkG X := fun X hX => hb X (by simp [hX])
      have hpos : 0 < Bk.length := hBk.1
      have hflat : (Bs' ++ [Bk]).flatten = Bs'.flatten ++ Bk := by
        rw [List.flatten_append]; simp
      have hM : (Bs' ++ [Bk]).flatten ++ P = Bs'.flatten ++ (Bk ++ P) := by
        rw [hflat, List.append_assoc]
      have hlenf : ((Bs' ++ [Bk]).flatten.length : Int)
          = ((Bs'.flatten.length + Bk.length : Nat) : Int) := by
        rw [hflat, List.length_append]
      have hMlen : ((Bs' ++ [Bk]).flatten ++ P).length
          = Bs'.flatten.length + Bk.length + P.length := by
        rw [hflat, List.length_append, List.length_append]
      have hentR : ∀ i, Bs'.flatten.length ≤ i →
          ent ((Bs' ++ [Bk]).flatten ++ P) i 0
            = ent (Bk ++ P) (i - Bs'.flatten.length) 0 := by
        intro i hi; rw [hM]; exact ent_append _ _ i 0 hi
      have hentBk : ∀ i, i < Bk.length → ent (Bk ++ P) i 0 = ent Bk i 0 :=
        fun i hi => ent_append_left _ _ i 0 hi
      have hentL : ∀ i, i < Bs'.flatten.length →
          ent ((Bs' ++ [Bk]).flatten ++ P) i 0 = ent Bs'.flatten i 0 := by
        intro i hi; rw [hM]; exact ent_append_left _ _ i 0 hi
      have hroot : ent ((Bs' ++ [Bk]).flatten ++ P) Bs'.flatten.length 0 = ent Bk 0 0 := by
        rw [hentR _ (Nat.le_refl _),
          show Bs'.flatten.length - Bs'.flatten.length = 0 from by omega, hentBk 0 hpos]
      have hkey : ∀ i, i < Bs'.flatten.length → ent Bk 0 0 ≤ ent Bs'.flatten i 0 := by
        intro i hi
        have h := hmin Bs'.length (by simp) i
        rw [show ((Bs' ++ [Bk]).take Bs'.length) = Bs' from by
            rw [take_app_left _ _ _ (Nat.le_refl _), List.take_length],
          show ((Bs' ++ [Bk]).getD Bs'.length []) = Bk from by
            rw [getD_app_right _ _ _ _ (Nat.le_refl _),
              show Bs'.length - Bs'.length = 0 from by omega]
            rfl] at h
        exact h hi
      have hnop : parent ((Bs' ++ [Bk]).flatten ++ P) 0 Bs'.flatten.length = none := by
        refine parent0_none_of_min _ _ ?_
        intro i hi
        rw [hroot, hentL i hi]
        exact hkey i hi
      have hj1 : Bs'.flatten.length + Bk.length - 1
          < ((Bs' ++ [Bk]).flatten ++ P).length := by rw [hMlen]; omega
      have hfa : ((fAnc (psM ((Bs' ++ [Bk]).flatten ++ P)) 0
          ((Bs'.flatten.length + Bk.length - 1 : Nat) : Int) 0).getLast?).getD 0
            = ((Bs'.flatten.length : Nat) : Int) := by
        rcases Nat.lt_or_ge Bs'.flatten.length (Bs'.flatten.length + Bk.length - 1)
          with hlt | hge
        · refine fAnc_last _ Bs'.flatten.length _ hnop hj1 hlt ⟨hlt, ?_⟩
          intro p h1 h2
          rw [hroot, hentR p (by omega), hentBk (p - Bs'.flatten.length) (by omega)]
          exact hBk.2 (p - Bs'.flatten.length) (by omega) (by omega)
        · have heq : Bs'.flatten.length + Bk.length - 1 = Bs'.flatten.length := by omega
          rw [heq]
          exact fAnc_last_self _ Bs'.flatten.length hnop (by rw [heq] at hj1; exact hj1)
      have hmin' : ∀ k, k < Bs'.length → ∀ i, i < ((Bs'.take k).flatten).length →
          ent (Bs'.getD k []) 0 0 ≤ ent ((Bs'.take k).flatten) i 0 := by
        intro k hk i hi
        have h := hmin k (by simp; omega) i
        rw [take_app_left _ _ _ (by omega), getD_app_left _ _ _ _ hk] at h
        exact h hi
      show (if (((Bs' ++ [Bk]).flatten.length : Int) - 1) < 0 then acc
            else ppairAux g (psM ((Bs' ++ [Bk]).flatten ++ P))
              (((fAnc (psM ((Bs' ++ [Bk]).flatten ++ P)) 0
                  (((Bs' ++ [Bk]).flatten.length : Int) - 1) 0).getLast?).getD 0 - 1)
              (slice (psM ((Bs' ++ [Bk]).flatten ++ P))
                (((fAnc (psM ((Bs' ++ [Bk]).flatten ++ P)) 0
                  (((Bs' ++ [Bk]).flatten.length : Int) - 1) 0).getLast?).getD 0)
                ((((Bs' ++ [Bk]).flatten.length : Int) - 1) + 1) :: acc)) = _
      rw [hlenf, if_neg (by omega),
        show (((Bs'.flatten.length + Bk.length : Nat) : Int) - 1)
          = ((Bs'.flatten.length + Bk.length - 1 : Nat) : Int) from by omega,
        hfa,
        show ((Bs'.flatten.length + Bk.length - 1 : Nat) : Int) + 1
          = ((Bs'.flatten.length + Bk.length : Nat) : Int) from by omega,
        hM, slice_block Bs'.flatten Bk P,
        ih Bs' (Bk ++ P) (psM Bk :: acc) hb' hmin' (by
          rw [List.length_append] at hlen; simp at hlen ⊢; omega)]
      simp

end

/-! ## §25 THE FOLD COLLAPSES — the matrix-level half

§23 measured what `red`'s fold does to a `matB` matrix; this is the half of that case which
is about the fold and not about trees.  `Rows/Ladder.lean`'s `red_fold_open` leaves

    red (f+1) M = (List.range (brF M).length).foldl (init := jjSeq 0 tr) fun r J => r ++ <term J>

and a `foldl` of appends is a `flatten` (`foldl_append_range`), so once every term returns
its own branch the whole thing is `jjSeq 0 tr ++ (brF M).flatten`.  That is `red_fold_id`:
its hypothesis `hterm` is exactly §23's third measurement — the rebuild
`(jnJ+1, nJ+1) :: derp bJ` gives `bJ` back and the shift puts it where it was — and its
`hsplit` is "the diagonal and the branches partition the matrix".

    red_fold_id : … → (∀ J < br.length, <the fold's J-th term> = br.getD J [])
                    → jjSeq 0 tr ++ br.flatten = M → red (f+1) M = M

`red_diag_id` is the companion for a matrix that IS the diagonal, where `trMax` reaches the
end and `red_jj` fires instead.

WHAT IS LEFT is the tree half: for `M = psM (matB (nd 0 nil a) 0)` in normal form, produce
`tr`, `br` and the three hypotheses — `trMax M` is the leftmost path, `brF M` the subtrees
hanging off it (via §24's `ppairAux_blocksG`), and the row-1 parent of a branch root is the
spine column one below its level. -/

section
open Trans.Recal

theorem foldl_append_range (g : Nat → PS) : ∀ (n : Nat) (init : PS),
    (List.range n).foldl (fun r J => r ++ g J) init
      = init ++ ((List.range n).map g).flatten := by
  intro n
  induction n with
  | zero => intro init; simp
  | succ k ih =>
    intro init
    rw [List.range_succ, List.foldl_append, ih init, List.map_append, List.flatten_append]
    simp [List.append_assoc]

theorem fold_to_flatten (g : Nat → PS) (br : List PS) (init : PS)
    (hg : ∀ J, J < br.length → g J = br.getD J []) :
    (List.range br.length).foldl (fun r J => r ++ g J) init = init ++ br.flatten := by
  rw [foldl_append_range g br.length init,
    List.map_congr_left (fun J hJ => hg J (List.mem_range.mp hJ)),
    map_getD_range ([] : PS) br]

/-- **畳み込みが行列を再現する条件。** 各項が自分の枝を返せば `red` は恒等。 -/
theorem red_fold_id (M : PS) (f : Nat) (tr : Int) (br : List PS)
    (hzero : isZeroP M = false) (hprin : isPrincipalP M = true)
    (hg0 : gp0 M 0 = 0) (hg1 : gp1 M 0 = 0)
    (htr : trMax M = tr) (hne : (tr == lenI M - 1) = false)
    (hbr : brF M = br)
    (hterm : ∀ J, J < br.length →
      incrFirst (red f (((joints M).getD J 0 + 1,
          (if gp1 (br.getD J []) 0 == 0 then (-1 : Int)
           else fpar M 1 ((firstNodes M).getD J 0) 0) + 1) :: derp (br.getD J [])))
        ((joints M).getD J 0 - (if gp1 (br.getD J []) 0 == 0 then (-1 : Int)
           else fpar M 1 ((firstNodes M).getD J 0) 0)) = br.getD J [])
    (hsplit : jjSeq 0 tr ++ br.flatten = M) :
    red (f + 1) M = M := by
  rw [Rows.Ladder.red_fold_open M f tr hzero hprin hg0 hg1 htr hne, hbr]
  show (List.range br.length).foldl (fun r J => r ++
      incrFirst (red f (((joints M).getD J 0 + 1,
          (if gp1 (br.getD J []) 0 == 0 then (-1 : Int)
           else fpar M 1 ((firstNodes M).getD J 0) 0) + 1) :: derp (br.getD J [])))
        ((joints M).getD J 0 - (if gp1 (br.getD J []) 0 == 0 then (-1 : Int)
           else fpar M 1 ((firstNodes M).getD J 0) 0)))
      (jjSeq 0 tr) = M
  rw [fold_to_flatten _ br (jjSeq 0 tr) hterm, hsplit]

/-- 枝が無い場合: 行列が対角そのもの。 -/
theorem red_diag_id (M : PS) (f : Nat)
    (hzero : isZeroP M = false) (hprin : isPrincipalP M = true)
    (hg0 : gp0 M 0 = 0) (hg1 : gp1 M 0 = 0)
    (htr : trMax M = lenI M - 1) (hM : jjSeq 0 (lenI M - 1) = M) :
    red (f + 1) M = M := by
  rw [Rows.Ladder.red_jj M f hzero hprin hg0 hg1 htr, hM]

end

/-! ## §26 `trMax` IS "DEPTH AND LEVEL BOTH GO UP"

The tree half of §25 starts with the diagonal, and the diagonal is `trMax`, and `trMax` is
`isParentP … 1` repeated.  That test unfolds to something completely local:

    isParentP M 1 (j+1) j = true  ↔  ent M j 0 < ent M (j+1) 0  ∧  ent M j 1 < ent M (j+1) 1

— the next column must be strictly deeper AND strictly higher.  The reason both searches
collapse to one step is the LOWER BOUND: `isParentP … j` runs `fpar … j`, whose scan may not
look further left than `j` itself, so `fpar0` either hits `j` on its first try or runs out of
room, and `fpar1` then either accepts `j` or restarts a scan that has no room at all
(`fpar0_self`).

On a `matB` matrix the two halves say exactly what one expects of a tree: the next column in
preorder is deeper precisely when it is a CHILD of this one, and under the normal form
(§19) a child's level is at most one more than its parent's, so "strictly higher" pins it to
EXACTLY one more.  That is why the run `0 … trMax M` comes out as `jjSeq 0 tr` and not merely
as some increasing path.

`trMax_of` packages it: give the position where the test first fails — or say the matrix ends
there — and `trMax` is that position. -/

section
open Trans.Recal

theorem lenI_psM (M : Matrix) : lenI (psM M) = ((M.length : Nat) : Int) := by
  show (((psM M).length : Nat) : Int) = _
  rw [psM_len]

/-- 自分自身を下限にすると親は無い。 -/
theorem fpar0_self (M : Matrix) (j : Nat) :
    fpar0 (psM M) ((j : Nat) : Int) ((j : Nat) : Int) = -1 := by
  by_cases h : ((j : Nat) : Int) < 0 ∨ ((j : Nat) : Int) ≥ lenI (psM M)
  · show (if ((j : Nat) : Int) < 0 ∨ ((j : Nat) : Int) ≥ lenI (psM M) then (-1 : Int) else _) = _
    rw [if_pos h]
  · rw [fpar0_in _ _ _ h]
    exact fpar0Aux_neg _ _ _ _ _ (by omega)

/-- 隣の列が行 0 の親か。 -/
theorem fpar0_succ (M : Matrix) (j : Nat) (hj : j + 1 < M.length) :
    fpar0 (psM M) (((j : Nat) : Int) + 1) ((j : Nat) : Int)
      = if ent M j 0 < ent M (j + 1) 0 then ((j : Nat) : Int) else -1 := by
  rw [fpar0_in _ _ _ (by rw [lenI_psM]; omega),
    show (((j : Nat) : Int) + 1) = ((j + 1 : Nat) : Int) from by omega, psM_gp0,
    show ((j + 1 : Nat) : Int) - 1 = ((j : Nat) : Int) from by omega]
  by_cases h : ent M j 0 < ent M (j + 1) 0
  · rw [if_pos h]
    exact fpar0Aux_hit _ _ _ _ _ (by omega) (by rw [psM_gp0]; omega)
  · rw [if_neg h]
    show (if ((j : Nat) : Int) < ((j : Nat) : Int) then (-1 : Int)
          else if gp0 (psM M) ((j : Nat) : Int) < ((ent M (j + 1) 0 : Nat) : Int)
               then ((j : Nat) : Int)
               else fpar0Aux (psM M).length (psM M) ((ent M (j + 1) 0 : Nat) : Int)
                      (((j : Nat) : Int) - 1) ((j : Nat) : Int)) = -1
    rw [if_neg (by omega), psM_gp0, if_neg (by omega),
      fpar0Aux_neg _ _ _ _ _ (by omega)]

/-- **隣の列が行 1 の親であるのは、深さと段の両方が真に増えるときちょうど。** -/
theorem fpar_one_succ (M : Matrix) (j : Nat) (hj : j + 1 < M.length) :
    fpar (psM M) 1 (((j : Nat) : Int) + 1) ((j : Nat) : Int)
      = if ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1
        then ((j : Nat) : Int) else -1 := by
  rw [Rows.Ladder.fpar1_unfold _ _ _ (by rw [lenI_psM]; omega)]
  show (let z := fpar0 (psM M) (((j : Nat) : Int) + 1) ((j : Nat) : Int)
        if z < ((j : Nat) : Int) then (-1 : Int)
        else if gp1 (psM M) z < gp1 (psM M) (((j : Nat) : Int) + 1) then z
        else fpar1Aux (psM M).length (psM M) (gp1 (psM M) (((j : Nat) : Int) + 1)) z
               ((j : Nat) : Int)) = _
  rw [fpar0_succ M j hj]
  by_cases h0 : ent M j 0 < ent M (j + 1) 0
  · rw [if_pos h0, if_neg (by omega),
      show (((j : Nat) : Int) + 1) = ((j + 1 : Nat) : Int) from by omega,
      psM_gp1, psM_gp1]
    by_cases h1 : ent M j 1 < ent M (j + 1) 1
    · rw [if_pos (by omega), if_pos ⟨h0, h1⟩]
    · rw [if_neg (by omega), if_neg (by intro hc; exact h1 hc.2)]
      show fpar1Aux (psM M).length (psM M) ((ent M (j + 1) 1 : Nat) : Int)
        ((j : Nat) : Int) ((j : Nat) : Int) = -1
      cases hL : (psM M).length with
      | zero => rfl
      | succ g =>
        show (let z := fpar0 (psM M) ((j : Nat) : Int) ((j : Nat) : Int)
              if z < ((j : Nat) : Int) then (-1 : Int) else _) = _
        rw [fpar0_self M j, if_pos (by omega)]
  · rw [if_neg h0, if_pos (by omega), if_neg (by intro hc; exact h0 hc.1)]

/-- `isParentP` の同じ形。 -/
theorem isParentP_succ_iff (M : Matrix) (j : Nat) (hj : j + 1 < M.length) :
    isParentP (psM M) 1 (((j : Nat) : Int) + 1) ((j : Nat) : Int) = true
      ↔ (ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1) := by
  show (decide ((0 : Int) ≤ ((j : Nat) : Int)) && decide (((j : Nat) : Int) < lenI (psM M))
    && (((j : Nat) : Int) == fpar (psM M) 1 (((j : Nat) : Int) + 1) ((j : Nat) : Int))) = true ↔ _
  rw [decide_eq_true (show (0 : Int) ≤ ((j : Nat) : Int) from by omega),
    decide_eq_true (show ((j : Nat) : Int) < lenI (psM M) from by rw [lenI_psM]; omega),
    fpar_one_succ M j hj]
  constructor
  · intro h
    by_cases hc : ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1
    · exact hc
    · exfalso
      rw [if_neg hc] at h
      simp at h
  · intro hc
    rw [if_pos hc]
    show (true && true && (((j : Nat) : Int) == ((j : Nat) : Int))) = true
    rw [beqI_self]
    rfl

/-- 右端では隣が無いので親でもない。 -/
theorem isParentP_succ_oob (M : Matrix) (j : Nat) (hj : M.length ≤ j + 1) :
    isParentP (psM M) 1 (((j : Nat) : Int) + 1) ((j : Nat) : Int) = false := by
  refine isParentP_of_ne _ _ _ _ ?_
  rw [fpar_oob _ _ _ _ (by rw [lenI_psM]; omega)]
  exact decide_eq_false (by omega)

/-- **`trMax` は「深さと段が両方増える」最初に破れる位置。** -/
theorem trMax_of (M : Matrix) (t : Nat) (hlen : t < M.length)
    (hkeep : ∀ j, j < t → ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1)
    (hstop : M.length ≤ t + 1
      ∨ ¬(ent M t 0 < ent M (t + 1) 0 ∧ ent M t 1 < ent M (t + 1) 1)) :
    trMax (psM M) = ((t : Nat) : Int) := by
  refine Rows.Ladder.trMax_eq (psM M) t (by rw [psM_len]; omega)
    (fun j hj => (isParentP_succ_iff M j (by omega)).mpr (hkeep j hj)) ?_
  rcases hstop with h | h
  · exact isParentP_succ_oob M t h
  · cases hres : isParentP (psM M) 1 (((t : Nat) : Int) + 1) ((t : Nat) : Int) with
    | false => rfl
    | true =>
      rcases Nat.lt_or_ge (t + 1) M.length with hlt | hge
      · exact absurd ((isParentP_succ_iff M t hlt).mp hres) h
      · rw [isParentP_succ_oob M t hge] at hres
        exact absurd hres (by simp)

end

end Evidence.Region
