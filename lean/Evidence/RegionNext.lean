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

/-! ## §27 THE SPINE IS THE DIAGONAL

§26 turned `trMax` into a local test on consecutive columns.  This turns that test into the
shape of the first `trMax M + 1` columns, and it does so WITHOUT computing `trMax` from the
tree — the run's own condition is enough, because `matB` bounds each step from the other
side:

    matB_step_depth : ent (matB t d) (j+1) 0  ≤  ent (matB t d) j 0 + 1
    matB_step_lvl   : (the depth stepped up by exactly one)
                      →  ent (matB t d) (j+1) 1  ≤  ent (matB t d) j 1 + 1     [needs `nfLe`]

The first is the preorder: the next column is a child (one deeper), a sibling, or a return
up the tree.  The second is the NORMAL FORM: the depth stepping up by one says the next
column is a child, and §19 caps a child's level at its parent's plus one.  Squeeze either
against `trMax`'s "strictly greater" and the step becomes an equality, so along the run

    ent M j 0 = ent M 0 0 + j        and        ent M j 1 = ent M 0 1 + j

(`spine_step`).  On `matB s 0` with `s` a single root of level 0 both bases are `0`, so the
run is `(0,0)(1,1)(2,2)…` and `take_jjSeq` reads it off as `jjSeq 0 tr` — the `hsplit` half
of §25's `red_fold_id`, and the reason `red` cuts a diagonal rather than an arbitrary path.

`headLvl` (the leftmost summand's level) is what `matB`'s first column carries, and
`headLvl_le` is the normal form seen from there. -/

section
open Trans.Recal

theorem ent_nil (j y : Nat) : ent ([] : Matrix) j y = 0 := by
  show ((([] : Matrix).getD j [])).getD y 0 = 0
  rw [show ([] : Matrix).getD j [] = [] from by simp]
  rfl

/-- 最左の最上位の加数の段。 -/
def headLvl : B → Nat
  | .nil => 0
  | .nd v .nil _ => v
  | .nd _ r _ => headLvl r

theorem matB_head0 : ∀ (t : B) (d : Nat), t ≠ .nil → ent (matB t d) 0 0 = d := by
  intro t
  induction t with
  | nil => intro _ h; exact absurd rfl h
  | nd v r a ihr _ =>
    intro d _
    cases r with
    | nil => rfl
    | nd v' r' a' =>
      show ent (matB (B.nd v' r' a') d ++ ([d, v] :: matB a (d + 1))) 0 0 = d
      rw [ent_append_left _ _ 0 0
        (matB_len_pos (B.nd v' r' a') d (by intro h; exact B.noConfusion h))]
      exact ihr d (by intro h; exact B.noConfusion h)

theorem matB_head1 : ∀ (t : B) (d : Nat), t ≠ .nil → ent (matB t d) 0 1 = headLvl t := by
  intro t
  induction t with
  | nil => intro _ h; exact absurd rfl h
  | nd v r a ihr _ =>
    intro d _
    cases r with
    | nil => rfl
    | nd v' r' a' =>
      show ent (matB (B.nd v' r' a') d ++ ([d, v] :: matB a (d + 1))) 0 1
        = headLvl (B.nd v (B.nd v' r' a') a)
      rw [ent_append_left _ _ 0 1
        (matB_len_pos (B.nd v' r' a') d (by intro h; exact B.noConfusion h))]
      show ent (matB (B.nd v' r' a') d) 0 1 = headLvl (B.nd v' r' a')
      exact ihr d (by intro h; exact B.noConfusion h)

/-- 標準形なら最左の段も上限以下。 -/
theorem headLvl_le : ∀ (t : B) (m : Nat), nfLe m t = true → t ≠ .nil → headLvl t ≤ m := by
  intro t
  induction t with
  | nil => intro _ _ h; exact absurd rfl h
  | nd v r a ihr _ =>
    intro m h _
    obtain ⟨h1, h2, _⟩ := (nfLe_nd_iff m v r a).mp h
    cases r with
    | nil => exact h1
    | nd v' r' a' =>
      show headLvl (B.nd v' r' a') ≤ m
      exact ihr m h2 (by intro hc; exact B.noConfusion hc)

/-- 深さは 1 列で高々 1 しか増えない。 -/
theorem matB_step_depth : ∀ (t : B) (d j : Nat),
    ent (matB t d) (j + 1) 0 ≤ ent (matB t d) j 0 + 1 := by
  intro t
  induction t with
  | nil => intro d j; show ent [] (j + 1) 0 ≤ _; rw [ent_zero_of_ge_len [] (j + 1) (by simp)]; omega
  | nd v r a ihr iha =>
    intro d j
    have hX : matB (B.nd v r a) d = matB r d ++ ([d, v] :: matB a (d + 1)) := rfl
    have hL : (matB r d).length = (matB r d).length := rfl
    rcases Nat.lt_or_ge (j + 1) (matB r d).length with hj | hj
    · rw [hX, ent_append_left _ _ (j + 1) 0 hj, ent_append_left _ _ j 0 (by omega)]
      exact ihr d j
    · rcases Nat.lt_or_ge j (matB r d).length with hj2 | hj2
      · -- j is the last column of the prefix, j+1 is the node column
        have hje : j + 1 = (matB r d).length := by omega
        rw [hX, ent_append _ _ (j + 1) 0 (by omega), hje,
          show (matB r d).length - (matB r d).length = 0 from by omega,
          ent_append_left _ _ j 0 hj2]
        have := matB_col_lb r d _ (getD_mem (matB r d) [] j hj2)
        show d ≤ ent (matB r d) j 0 + 1
        show d ≤ ((matB r d).getD j []).getD 0 0 + 1
        omega
      · -- both at or past the node column
        rw [hX, ent_append _ _ (j + 1) 0 (by omega), ent_append _ _ j 0 hj2]
        obtain ⟨i, hi⟩ : ∃ i, j = (matB r d).length + i := ⟨j - (matB r d).length, by omega⟩
        rw [hi, show (matB r d).length + i - (matB r d).length = i from by omega,
          show (matB r d).length + i + 1 - (matB r d).length = i + 1 from by omega]
        cases i with
        | zero =>
          show ent ([d, v] :: matB a (d + 1)) 1 0 ≤ ent ([d, v] :: matB a (d + 1)) 0 0 + 1
          show ent (matB a (d + 1)) 0 0 ≤ d + 1
          cases a with
          | nil => show ent [] 0 0 ≤ d + 1; rw [ent_zero_of_ge_len [] 0 (by simp)]; omega
          | nd v'' r'' a'' =>
            rw [matB_head0 (B.nd v'' r'' a'') (d + 1) (by intro hc; exact B.noConfusion hc)]
            omega
        | succ k =>
          show ent ([d, v] :: matB a (d + 1)) (k + 2) 0
            ≤ ent ([d, v] :: matB a (d + 1)) (k + 1) 0 + 1
          exact iha (d + 1) k

/-- **深さがちょうど 1 増えるなら段も高々 1 しか増えない。** 標準形が効くところ。 -/
theorem matB_step_lvl : ∀ (t : B) (m d j : Nat), nfLe m t = true →
    ent (matB t d) (j + 1) 0 = ent (matB t d) j 0 + 1 →
    ent (matB t d) (j + 1) 1 ≤ ent (matB t d) j 1 + 1 := by
  intro t
  induction t with
  | nil =>
    intro m d j _ _
    show ent [] (j + 1) 1 ≤ ent ([] : Matrix) j 1 + 1
    rw [ent_nil, ent_nil]
    omega
  | nd v r a ihr iha =>
    intro m d j hnf hstep
    obtain ⟨_, hr, ha⟩ := (nfLe_nd_iff m v r a).mp hnf
    have hX : matB (B.nd v r a) d = matB r d ++ ([d, v] :: matB a (d + 1)) := rfl
    rcases Nat.lt_or_ge (j + 1) (matB r d).length with hj | hj
    · rw [hX, ent_append_left _ _ (j + 1) 1 hj, ent_append_left _ _ j 1 (by omega)]
      refine ihr m d j hr ?_
      rw [hX, ent_append_left _ _ (j + 1) 0 hj, ent_append_left _ _ j 0 (by omega)] at hstep
      exact hstep
    · rcases Nat.lt_or_ge j (matB r d).length with hj2 | hj2
      · exfalso
        have hje : j + 1 = (matB r d).length := by omega
        rw [hX, ent_append _ _ (j + 1) 0 (by omega), hje,
          show (matB r d).length - (matB r d).length = 0 from by omega,
          ent_append_left _ _ j 0 hj2] at hstep
        have hlb : d ≤ ent (matB r d) j 0 :=
          matB_col_lb r d _ (getD_mem (matB r d) [] j hj2)
        have hstep' : d = ent (matB r d) j 0 + 1 := hstep
        omega
      · rw [hX, ent_append _ _ (j + 1) 1 (by omega), ent_append _ _ j 1 hj2]
        obtain ⟨i, hi⟩ : ∃ i, j = (matB r d).length + i := ⟨j - (matB r d).length, by omega⟩
        rw [hi, show (matB r d).length + i - (matB r d).length = i from by omega,
          show (matB r d).length + i + 1 - (matB r d).length = i + 1 from by omega]
        cases i with
        | zero =>
          show ent (matB a (d + 1)) 0 1 ≤ v + 1
          cases a with
          | nil =>
            show ent ([] : Matrix) 0 1 ≤ v + 1
            rw [ent_nil]
            omega
          | nd v'' r'' a'' =>
            rw [matB_head1 (B.nd v'' r'' a'') (d + 1) (by intro hc; exact B.noConfusion hc)]
            exact headLvl_le _ (v + 1) ha (by intro hc; exact B.noConfusion hc)
        | succ k =>
          show ent ([d, v] :: matB a (d + 1)) (k + 2) 1
            ≤ ent ([d, v] :: matB a (d + 1)) (k + 1) 1 + 1
          show ent (matB a (d + 1)) (k + 1) 1 ≤ ent (matB a (d + 1)) k 1 + 1
          refine iha (v + 1) (d + 1) k ha ?_
          rw [hX, ent_append _ _ (j + 1) 0 (by omega), ent_append _ _ j 0 hj2, hi,
            show (matB r d).length + (k + 1) - (matB r d).length = k + 1 from by omega,
            show (matB r d).length + (k + 1) + 1 - (matB r d).length = k + 2 from by omega] at hstep
          exact hstep

/-! ### the spine is the diagonal -/

/-- 走りの上では深さも段もちょうど 1 ずつ増える。 -/
theorem spine_step (t : B) (m d : Nat) (hnf : nfLe m t = true) (tr : Nat)
    (hrun : ∀ j, j < tr → ent (matB t d) j 0 < ent (matB t d) (j + 1) 0
      ∧ ent (matB t d) j 1 < ent (matB t d) (j + 1) 1) :
    ∀ j, j ≤ tr → ent (matB t d) j 0 = ent (matB t d) 0 0 + j
      ∧ ent (matB t d) j 1 = ent (matB t d) 0 1 + j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨by omega, by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨h0, h1⟩ := ih (by omega)
    obtain ⟨hr0, hr1⟩ := hrun k (by omega)
    have hd : ent (matB t d) (k + 1) 0 = ent (matB t d) k 0 + 1 := by
      have := matB_step_depth t d k
      omega
    have hl := matB_step_lvl t m d k hnf hd
    exact ⟨by omega, by omega⟩

theorem take_eq_map_range {α : Type _} (dd : α) : ∀ (n : Nat) (l : List α), n ≤ l.length →
    l.take n = (List.range n).map (fun i => l.getD i dd) := by
  intro n
  induction n with
  | zero => intro l _; rfl
  | succ k ih =>
    intro l h
    rw [List.take_add_one, ih l (by omega), List.range_succ, List.map_append]
    have : l[k]? = some (l.getD k dd) := by
      rw [List.getD_eq_getElem?_getD, show l[k]? = some l[k] from
        List.getElem?_eq_getElem (by omega)]
      rfl
    rw [this]
    rfl

/-- **対角の切り出し。** 走りの上では最初の `tr+1` 列が `jjSeq 0 tr` そのもの。 -/
theorem take_jjSeq (M : Matrix) (tr : Nat) (hlen : tr < M.length)
    (hcol : ∀ j, j ≤ tr → ent M j 0 = j ∧ ent M j 1 = j) :
    (psM M).take (tr + 1) = jjSeq 0 ((tr : Nat) : Int) := by
  rw [take_eq_map_range ((0 : Int), (0 : Int)) (tr + 1) (psM M) (by rw [psM_len]; omega),
    jjSeq_zero tr]
  refine List.map_congr_left (fun i hi => ?_)
  have hile : i ≤ tr := by have := List.mem_range.mp hi; omega
  rw [getD_psM, (hcol i hile).1, (hcol i hile).2]

end

/-! ## §28 THE NORMAL FORM, SEEN FROM THE MATRIX

§27's `matB_step_lvl` bounds a column's level by the PREVIOUS column's, which is the parent
only when the previous column happens to be it.  The fold needs the general statement — a
branch root's level against its joint's — and the joint is far to the left:

    matB_lvl_le_par : `k` is the tree parent of `i`  →  level i ≤ level k + 1

"tree parent" is spelled `LMin (matB t d) k i` together with `ent k 0 + 1 = ent i 0`, and by
§8 and §18.1 that is exactly what `fpar0`/`BMS.parent` return.  The induction is the same
three-way split as everywhere in this file, and two of the three cases are VACUOUS: a `k` in
the prefix cannot be the parent of anything at or past the node column, because the node
column sits at depth `d` and the prefix never goes above `d`.  The one real case is `k` = the
node column, where the claim becomes "every top-level root of the argument has level at most
`v + 1`" — which is `nfLe (v+1) a` read at the matrix (`matB_top_lvl`).

`par_depth` is the other half of "tree parent": what `BMS.parent` returns is always EXACTLY
one step shallower.  That needs no normal form — it follows from §27's `matB_step_depth`
alone, since the column just after the parent is either `i` itself or too deep to be a
candidate, and either way it caps `ent i 0` at `ent p 0 + 1`.

Together, `lvl_le_fpar`: the level of a column is at most one more than the level of the
column `fpar0` calls its parent.  That is the inequality that makes §23's measured identity
`(jnJ+1, nJ+1) :: derp bJ = bJ` true — a branch root of level `u` hanging off a spine column
of level (= index) `jnJ` has `u ≤ jnJ + 1`, so its row-1 parent is spine column `u - 1`. -/

section
open Trans.Recal

theorem ent_oob (M : Matrix) (j y : Nat) (h : M.length ≤ j) : ent M j y = 0 := by
  show ((M.getD j []).getD y 0) = 0
  rw [show M.getD j [] = [] from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]]
  rfl

/-- **底の深さにいる列は最上位の加数の根なので、段は上限以下。** -/
theorem matB_top_lvl : ∀ (a : B) (m e i : Nat), nfLe m a = true →
    ent (matB a e) i 0 = e → ent (matB a e) i 1 ≤ m := by
  intro a
  induction a with
  | nil => intro m e i _ _; show ent ([] : Matrix) i 1 ≤ m; rw [ent_nil]; omega
  | nd v r b ihr ihb =>
    intro m e i hnf hdep
    obtain ⟨h1, hr, hb⟩ := (nfLe_nd_iff m v r b).mp hnf
    have hX : matB (B.nd v r b) e = matB r e ++ ([e, v] :: matB b (e + 1)) := rfl
    rcases Nat.lt_or_ge i (matB r e).length with hi | hi
    · rw [hX, ent_append_left _ _ i 1 hi]
      refine ihr m e i hr ?_
      rw [hX, ent_append_left _ _ i 0 hi] at hdep
      exact hdep
    · rw [hX, ent_append _ _ i 1 hi]
      obtain ⟨j, hj⟩ : ∃ j, i = (matB r e).length + j := ⟨i - (matB r e).length, by omega⟩
      rw [hj, show (matB r e).length + j - (matB r e).length = j from by omega]
      cases j with
      | zero => exact h1
      | succ k =>
        rw [hX, ent_append _ _ i 0 hi, hj,
          show (matB r e).length + (k + 1) - (matB r e).length = k + 1 from by omega] at hdep
        have hdep' : ent (matB b (e + 1)) k 0 = e := hdep
        show ent (matB b (e + 1)) k 1 ≤ m
        rcases Nat.lt_or_ge k (matB b (e + 1)).length with hk | hk
        · exfalso
          have hlb : e + 1 ≤ ent (matB b (e + 1)) k 0 :=
            matB_col_lb b (e + 1) _ (getD_mem (matB b (e + 1)) [] k hk)
          omega
        · rw [ent_oob _ k 1 hk]
          omega

/-- **標準形は「段は木の親の段 + 1 以下」として行列に現れる。** -/
theorem matB_lvl_le_par : ∀ (t : B) (m d : Nat), nfLe m t = true → ∀ (k i : Nat),
    LMin (matB t d) k i → ent (matB t d) k 0 + 1 = ent (matB t d) i 0 →
    ent (matB t d) i 1 ≤ ent (matB t d) k 1 + 1 := by
  intro t
  induction t with
  | nil =>
    intro m d _ k i _ _
    show ent ([] : Matrix) i 1 ≤ ent ([] : Matrix) k 1 + 1
    rw [ent_nil, ent_nil]
    omega
  | nd v r a ihr iha =>
    intro m d hnf k i hlm hdep
    obtain ⟨h1, hr, ha⟩ := (nfLe_nd_iff m v r a).mp hnf
    have hX : matB (B.nd v r a) d = matB r d ++ ([d, v] :: matB a (d + 1)) := rfl
    have hki : k < i := hlm.1
    rcases Nat.lt_or_ge i (matB r d).length with hi | hi
    · -- both inside the prefix
      rw [hX, ent_append_left _ _ i 1 hi, ent_append_left _ _ k 1 (by omega)]
      refine ihr m d hr k i ⟨hki, ?_⟩ ?_
      · intro p hp1 hp2
        have := hlm.2 p hp1 hp2
        rw [hX, ent_append_left _ _ k 0 (by omega), ent_append_left _ _ p 0 (by omega)] at this
        exact this
      · rw [hX, ent_append_left _ _ i 0 hi, ent_append_left _ _ k 0 (by omega)] at hdep
        exact hdep
    · rcases Nat.lt_or_ge k (matB r d).length with hk | hk
      · -- k inside the prefix, i at or past the node column: impossible
        exfalso
        have hklb : d ≤ ent (matB r d) k 0 :=
          matB_col_lb r d _ (getD_mem (matB r d) [] k hk)
        have hkent : ent (matB (B.nd v r a) d) k 0 = ent (matB r d) k 0 := by
          rw [hX, ent_append_left _ _ k 0 hk]
        have hnode : ent (matB (B.nd v r a) d) (matB r d).length 0 = d := by
          rw [hX, ent_append _ _ (matB r d).length 0 (by omega),
            show (matB r d).length - (matB r d).length = 0 from by omega]
          rfl
        rcases Nat.eq_or_lt_of_le hi with hiL | hiL
        · -- i is the node column
          rw [hiL] at hnode
          omega
        · have := hlm.2 (matB r d).length (by omega) (by omega)
          omega
      · -- both at or past the node column
        obtain ⟨ki, hki'⟩ : ∃ z, k = (matB r d).length + z := ⟨k - (matB r d).length, by omega⟩
        obtain ⟨ii, hii'⟩ : ∃ z, i = (matB r d).length + z := ⟨i - (matB r d).length, by omega⟩
        rw [hX, ent_append _ _ i 1 (by omega), ent_append _ _ k 1 (by omega), hki', hii',
          show (matB r d).length + ki - (matB r d).length = ki from by omega,
          show (matB r d).length + ii - (matB r d).length = ii from by omega]
        rw [hX, ent_append _ _ i 0 (by omega), ent_append _ _ k 0 (by omega), hki', hii',
          show (matB r d).length + ki - (matB r d).length = ki from by omega,
          show (matB r d).length + ii - (matB r d).length = ii from by omega] at hdep
        cases ki with
        | zero =>
          -- k is the node column
          cases ii with
          | zero => exact absurd hki' (by omega)
          | succ jj =>
            have hd' : d + 1 = ent (matB a (d + 1)) jj 0 := hdep
            show ent (matB a (d + 1)) jj 1 ≤ v + 1
            exact matB_top_lvl a (v + 1) (d + 1) jj ha hd'.symm
        | succ jk =>
          cases ii with
          | zero => exact absurd hki' (by omega)
          | succ jj =>
            show ent (matB a (d + 1)) jj 1 ≤ ent (matB a (d + 1)) jk 1 + 1
            refine iha (v + 1) (d + 1) ha jk jj ⟨by omega, ?_⟩ hdep
            intro p hp1 hp2
            have := hlm.2 ((matB r d).length + 1 + p) (by omega) (by omega)
            rw [hX, ent_append _ _ ((matB r d).length + 1 + p) 0 (by omega),
              ent_append _ _ k 0 (by omega), hki',
              show (matB r d).length + (jk + 1) - (matB r d).length = jk + 1 from by omega,
              show (matB r d).length + 1 + p - (matB r d).length = p + 1 from by omega] at this
            exact this

/-- **木の親はちょうど 1 段浅い。** 深さが 1 列で高々 1 しか増えないことから。 -/
theorem par_depth (t : B) (d i p : Nat) (hp : parent (matB t d) 0 i = some p) :
    ent (matB t d) p 0 + 1 = ent (matB t d) i 0 := by
  obtain ⟨hmem, hmax⟩ := List.max?_eq_some_iff.mp hp
  have hpi : p < i := List.mem_range.mp (List.mem_filter.mp hmem).1
  have hlt : ent (matB t d) p 0 < ent (matB t d) i 0 :=
    of_decide_eq_true (List.mem_filter.mp hmem).2
  have hnext : ent (matB t d) i 0 ≤ ent (matB t d) (p + 1) 0 := by
    rcases Nat.eq_or_lt_of_le hpi with heq | hlt2
    · rw [show p + 1 = i from heq]
      omega
    · rcases Nat.lt_or_ge (ent (matB t d) (p + 1) 0) (ent (matB t d) i 0) with hc | hc
      · exfalso
        have : p + 1 ∈ (List.range i).filter
            (fun q => decide (ent (matB t d) q 0 < ent (matB t d) i 0)) :=
          List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), decide_eq_true hc⟩
        have := hmax _ this
        omega
      · exact hc
  have hstep := matB_step_depth t d p
  omega

/-- `fpar0` が返した親に対する標準形の形。 -/
theorem lvl_le_fpar (t : B) (m d : Nat) (hnf : nfLe m t = true) (i p : Nat)
    (hi : i < (matB t d).length)
    (hfp : fpar0 (psM (matB t d)) ((i : Nat) : Int) 0 = ((p : Nat) : Int)) :
    ent (matB t d) i 1 ≤ ent (matB t d) p 1 + 1 := by
  have hlm : LMin (matB t d) p i := lmin_of_fpar0 (matB t d) i p hi hfp
  refine matB_lvl_le_par t m d hnf p i hlm ?_
  refine par_depth t d i p ?_
  rw [fpar0_eq_parent (matB t d) i hi] at hfp
  cases hq : parent (matB t d) 0 i with
  | none =>
    rw [hq] at hfp
    exact absurd (show (-1 : Int) = ((p : Nat) : Int) from hfp) (by omega)
  | some q =>
    rw [hq] at hfp
    have : ((q : Nat) : Int) = ((p : Nat) : Int) := hfp
    rw [show q = p from by omega]

end

/-! ## §29 `trMax` COMPUTED, AND THE DIAGONAL CUT

§26 says what `trMax` is and §27 says what the run looks like, but both take the position as
given.  `runLen` produces it: walk right while "depth and level both go up", and stop.  It is
defined on the MATRIX, not on the tree, which is the point — nothing here needs to know how
the index is shaped, only that the two step bounds of §27 hold.

    trMax_runLen : trMax (psM M) = runLen M

and on a region matrix the run is the diagonal outright (`spine_diag_matB`): the root is at
depth 0 and level 0, §27 makes both go up by exactly one along the run, so column `j` is
`(j, j)` for every `j ≤ runLen M`.  With §27's `take_jjSeq` that is `red`'s `jjSeq 0 tr`, and
with `psM_split` the matrix is that diagonal followed by whatever is left.

So of §25's three hypotheses, `htr` is now `trMax_runLen` and half of `hsplit` is done.  What
remains is the other half — that the rest of the matrix is `brF M`'s blocks concatenated —
and `hterm`. -/

section
open Trans.Recal

/-- 「深さも段も真に増える」が続く長さ。 -/
def runAux (M : Matrix) : Nat → Nat → Nat
  | 0, j => j
  | f + 1, j =>
    if j + 1 < M.length ∧ ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1
    then runAux M f (j + 1) else j

def runLen (M : Matrix) : Nat := runAux M M.length 0

theorem runAux_spec (M : Matrix) : ∀ (f j : Nat), j < M.length → M.length ≤ j + f →
    runAux M f j < M.length
    ∧ j ≤ runAux M f j
    ∧ (∀ i, j ≤ i → i < runAux M f j →
        ent M i 0 < ent M (i + 1) 0 ∧ ent M i 1 < ent M (i + 1) 1)
    ∧ (M.length ≤ runAux M f j + 1
       ∨ ¬(ent M (runAux M f j) 0 < ent M (runAux M f j + 1) 0
           ∧ ent M (runAux M f j) 1 < ent M (runAux M f j + 1) 1)) := by
  intro f
  induction f with
  | zero => intro j h1 h2; exact absurd h2 (by omega)
  | succ g ih =>
    intro j h1 h2
    by_cases hc : j + 1 < M.length ∧ ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1
    · have hstep : runAux M (g + 1) j = runAux M g (j + 1) := by
        show (if j + 1 < M.length ∧ _ ∧ _ then runAux M g (j + 1) else j) = _
        rw [if_pos hc]
      obtain ⟨k1, k2, k3, k4⟩ := ih (j + 1) hc.1 (by omega)
      refine ⟨by rw [hstep]; exact k1, by rw [hstep]; omega, ?_, by rw [hstep]; exact k4⟩
      intro i hi1 hi2
      rw [hstep] at hi2
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
      · exact hc.2
      · exact k3 i (by omega) hi2
    · have hstep : runAux M (g + 1) j = j := by
        show (if j + 1 < M.length ∧ _ ∧ _ then runAux M g (j + 1) else j) = _
        rw [if_neg hc]
      rw [hstep]
      refine ⟨h1, Nat.le_refl _, fun i hi1 hi2 => absurd hi2 (by omega), ?_⟩
      rcases Nat.lt_or_ge (j + 1) M.length with hj | hj
      · exact Or.inr (fun hd => hc ⟨hj, hd⟩)
      · exact Or.inl hj

theorem runLen_lt (M : Matrix) (h : 0 < M.length) : runLen M < M.length :=
  (runAux_spec M M.length 0 h (by omega)).1

theorem runLen_run (M : Matrix) (h : 0 < M.length) : ∀ i, i < runLen M →
    ent M i 0 < ent M (i + 1) 0 ∧ ent M i 1 < ent M (i + 1) 1 :=
  fun i hi => (runAux_spec M M.length 0 h (by omega)).2.2.1 i (by omega) hi

theorem runLen_stop (M : Matrix) (h : 0 < M.length) :
    M.length ≤ runLen M + 1
    ∨ ¬(ent M (runLen M) 0 < ent M (runLen M + 1) 0
        ∧ ent M (runLen M) 1 < ent M (runLen M + 1) 1) :=
  (runAux_spec M M.length 0 h (by omega)).2.2.2

/-- **`trMax` は走りの長さ。** -/
theorem trMax_runLen (M : Matrix) (h : 0 < M.length) :
    trMax (psM M) = ((runLen M : Nat) : Int) :=
  trMax_of M (runLen M) (runLen_lt M h) (runLen_run M h) (runLen_stop M h)

/-- **領域の行列では走りの上で深さ = 段 = 添字。** -/
theorem spine_diag_matB (a : B) (hnf : nfLe 1 a = true) :
    ∀ j, j ≤ runLen (matB (.nd 0 .nil a) 0) →
      ent (matB (.nd 0 .nil a) 0) j 0 = j ∧ ent (matB (.nd 0 .nil a) 0) j 1 = j := by
  have hne : (B.nd 0 .nil a) ≠ .nil := by intro h; exact B.noConfusion h
  have hpos : 0 < (matB (B.nd 0 .nil a) 0).length := matB_len_pos _ 0 hne
  have hnf0 : nfLe 0 (B.nd 0 .nil a) = true := (nfLe_nd_iff 0 0 .nil a).mpr ⟨by omega, rfl, hnf⟩
  have h00 : ent (matB (B.nd 0 .nil a) 0) 0 0 = 0 := matB_head0 _ 0 hne
  have h01 : ent (matB (B.nd 0 .nil a) 0) 0 1 = 0 := by
    rw [matB_head1 _ 0 hne]
    rfl
  intro j hj
  obtain ⟨s0, s1⟩ := spine_step (B.nd 0 .nil a) 0 0 hnf0 (runLen (matB (B.nd 0 .nil a) 0))
    (fun i hi => runLen_run _ hpos i hi) j hj
  exact ⟨by omega, by omega⟩

/-- 対角と残りで行列が割れる。 -/
theorem psM_split (M : Matrix) (n : Nat) :
    (psM M).take n ++ (psM M).drop n = psM M := List.take_append_drop ..

end

/-! ## §30 `brF`, AND `hsplit` CLOSED

The last structural piece.  `brF M` is `ppair` of what follows the diagonal, and §24 says
`ppair` returns a block list once two things hold: each block's first column is strictly
shallower than the rest of ITS OWN block, and no column before a block is shallower than that
block's root.  Both are true of the RUNNING-MINIMUM decomposition, and that decomposition is
what `peel` computes:

    peel dd X    the maximal prefix of X strictly deeper than dd, and the rest
    blocks X     peel at the head's depth, then recurse on the rest

`peel`'s stopping condition gives the second property directly — the next block's root is the
first column not deeper than this one's, so the roots never go up as one walks right, and a
column can only be shallower than a later root if it is a root itself, which it is not.

    ppair_blocksG : ppair (psM X) = (blocks X).map psM
    brF_blocks    : brF (psM Mat) = (blocks (Mat.drop (runLen Mat + 1))).map psM
    brF_flatten   : (brF (psM Mat)).flatten = (psM Mat).drop (runLen Mat + 1)

and with §29's diagonal that is §25's second hypothesis outright:

    hsplit_matB : jjSeq 0 (runLen …) ++ (brF …).flatten = psM (matB (nd 0 nil a) 0)

NOTHING HERE IS ABOUT TREES.  `blocks` is defined on the matrix and the proofs never mention
`B`; what makes the decomposition the right one on a region matrix is only §27's step bounds,
which is why the same machinery will serve the branches at any depth.

What is left of the whole `red` proof is `hterm` — that the fold's `J`-th term returns the
`J`-th branch.  §23 measured it as an identity and §28 supplies the inequality it rests on. -/

section
open Trans.Recal

/-- `dd` より深い列の極大な接頭辞と、その残り。 -/
def peel (dd : Nat) : Matrix → Matrix × Matrix
  | [] => ([], [])
  | c :: cs =>
    if dd < c.getD 0 0 then (c :: (peel dd cs).1, (peel dd cs).2) else ([], c :: cs)

theorem peel_nil (dd : Nat) : peel dd [] = ([], []) := rfl

theorem peel_cons_pos (dd : Nat) (c : Col) (cs : Matrix) (h : dd < c.getD 0 0) :
    peel dd (c :: cs) = (c :: (peel dd cs).1, (peel dd cs).2) := by
  show (if dd < c.getD 0 0 then (c :: (peel dd cs).1, (peel dd cs).2)
        else ([], c :: cs)) = _
  rw [if_pos h]

theorem peel_cons_neg (dd : Nat) (c : Col) (cs : Matrix) (h : ¬(dd < c.getD 0 0)) :
    peel dd (c :: cs) = ([], c :: cs) := by
  show (if dd < c.getD 0 0 then (c :: (peel dd cs).1, (peel dd cs).2)
        else ([], c :: cs)) = _
  rw [if_neg h]

theorem peel_append : ∀ (dd : Nat) (X : Matrix), (peel dd X).1 ++ (peel dd X).2 = X := by
  intro dd X
  induction X with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : dd < c.getD 0 0
    · rw [peel_cons_pos dd c cs h]
      show c :: ((peel dd cs).1 ++ (peel dd cs).2) = c :: cs
      rw [ih]
    · rw [peel_cons_neg dd c cs h]
      rfl

theorem peel_len2 : ∀ (dd : Nat) (X : Matrix), (peel dd X).2.length ≤ X.length := by
  intro dd X
  induction X with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    by_cases h : dd < c.getD 0 0
    · rw [peel_cons_pos dd c cs h, List.length_cons]
      exact Nat.le_trans ih (by omega)
    · rw [peel_cons_neg dd c cs h]
      exact Nat.le_refl _

theorem peel_deep : ∀ (dd : Nat) (X : Matrix) (i : Nat), i < (peel dd X).1.length →
    dd < ent (peel dd X).1 i 0 := by
  intro dd X
  induction X with
  | nil => intro i h; rw [peel_nil] at h; exact absurd h (by simp)
  | cons c cs ih =>
    intro i h
    by_cases hc : dd < c.getD 0 0
    · rw [peel_cons_pos dd c cs hc]
      rw [peel_cons_pos dd c cs hc, List.length_cons] at h
      cases i with
      | zero => exact hc
      | succ k =>
        show dd < ent (peel dd cs).1 k 0
        exact ih k (by omega)
    · rw [peel_cons_neg dd c cs hc] at h
      exact absurd h (by simp)

theorem peel_stop : ∀ (dd : Nat) (X : Matrix), 0 < (peel dd X).2.length →
    ent (peel dd X).2 0 0 ≤ dd := by
  intro dd X
  induction X with
  | nil => intro h; rw [peel_nil] at h; exact absurd h (by simp)
  | cons c cs ih =>
    intro h
    by_cases hc : dd < c.getD 0 0
    · rw [peel_cons_pos dd c cs hc]
      rw [peel_cons_pos dd c cs hc] at h
      exact ih h
    · rw [peel_cons_neg dd c cs hc]
      show c.getD 0 0 ≤ dd
      omega

/-- 走る最小値で切ったブロック列。 -/
def blocks : Matrix → List Matrix
  | [] => []
  | c :: cs => (c :: (peel (c.getD 0 0) cs).1) :: blocks (peel (c.getD 0 0) cs).2
  termination_by X => X.length
  decreasing_by
    have h := peel_len2 (c.getD 0 0) cs
    simp only [List.length_cons]
    omega

theorem blocks_nil : blocks [] = [] := by rw [blocks]

theorem blocks_cons (c : Col) (cs : Matrix) :
    blocks (c :: cs)
      = (c :: (peel (c.getD 0 0) cs).1) :: blocks (peel (c.getD 0 0) cs).2 := by
  rw [blocks]

theorem blocks_flatten : ∀ (n : Nat) (X : Matrix), X.length ≤ n → (blocks X).flatten = X := by
  intro n
  induction n with
  | zero =>
    intro X h
    rw [show X = [] from List.eq_nil_of_length_eq_zero (by omega), blocks_nil]
    rfl
  | succ g ih =>
    intro X h
    cases X with
    | nil => rw [blocks_nil]; rfl
    | cons c cs =>
      rw [blocks_cons c cs, List.flatten_cons,
        ih (peel (c.getD 0 0) cs).2 (by
          have := peel_len2 (c.getD 0 0) cs
          rw [List.length_cons] at h
          omega)]
      show c :: ((peel (c.getD 0 0) cs).1 ++ (peel (c.getD 0 0) cs).2) = c :: cs
      rw [peel_append]

theorem blocks_head_blkG (c : Col) (cs : Matrix) :
    BlkG (c :: (peel (c.getD 0 0) cs).1) := by
  refine ⟨by simp, ?_⟩
  intro p hp hlen
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  show ent (c :: (peel (c.getD 0 0) cs).1) 0 0 < ent (peel (c.getD 0 0) cs).1 k 0
  refine peel_deep (c.getD 0 0) cs k ?_
  rw [List.length_cons] at hlen
  omega

theorem blocks_blkG : ∀ (n : Nat) (X : Matrix), X.length ≤ n → ∀ Bk ∈ blocks X, BlkG Bk := by
  intro n
  induction n with
  | zero =>
    intro X h Bk hBk
    rw [show X = [] from List.eq_nil_of_length_eq_zero (by omega), blocks_nil] at hBk
    exact absurd hBk (by simp)
  | succ g ih =>
    intro X h Bk hBk
    cases X with
    | nil => rw [blocks_nil] at hBk; exact absurd hBk (by simp)
    | cons c cs =>
      rw [blocks_cons c cs] at hBk
      rcases List.mem_cons.mp hBk with rfl | hBk
      · exact blocks_head_blkG c cs
      · refine ih (peel (c.getD 0 0) cs).2 ?_ Bk hBk
        have := peel_len2 (c.getD 0 0) cs
        rw [List.length_cons] at h
        omega

theorem blocks_root_le : ∀ (n : Nat) (X : Matrix), X.length ≤ n → ∀ k, k < (blocks X).length →
    ent ((blocks X).getD k []) 0 0 ≤ ent X 0 0 := by
  intro n
  induction n with
  | zero =>
    intro X h k hk
    rw [show X = [] from List.eq_nil_of_length_eq_zero (by omega), blocks_nil] at hk
    exact absurd hk (by simp)
  | succ g ih =>
    intro X h k hk
    cases X with
    | nil => rw [blocks_nil] at hk; exact absurd hk (by simp)
    | cons c cs =>
      rw [blocks_cons c cs] at hk ⊢
      cases k with
      | zero => exact Nat.le_refl _
      | succ j =>
        show ent ((blocks (peel (c.getD 0 0) cs).2).getD j []) 0 0 ≤ ent (c :: cs) 0 0
        have hlen : (peel (c.getD 0 0) cs).2.length ≤ g := by
          have := peel_len2 (c.getD 0 0) cs
          rw [List.length_cons] at h
          omega
        have hj : j < (blocks (peel (c.getD 0 0) cs).2).length := by
          rw [List.length_cons] at hk; omega
        have h1 := ih (peel (c.getD 0 0) cs).2 hlen j hj
        have h2 : ent (peel (c.getD 0 0) cs).2 0 0 ≤ c.getD 0 0 := by
          refine peel_stop (c.getD 0 0) cs ?_
          rcases Nat.eq_or_lt_of_le (Nat.zero_le (peel (c.getD 0 0) cs).2.length) with he | he
          · exfalso
            rw [show (peel (c.getD 0 0) cs).2 = [] from
              List.eq_nil_of_length_eq_zero he.symm, blocks_nil] at hj
            exact absurd hj (by simp)
          · exact he
        show _ ≤ c.getD 0 0
        omega

theorem blocks_min : ∀ (n : Nat) (X : Matrix), X.length ≤ n → ∀ k, k < (blocks X).length →
    ∀ i, i < (((blocks X).take k).flatten).length →
      ent ((blocks X).getD k []) 0 0 ≤ ent (((blocks X).take k).flatten) i 0 := by
  intro n
  induction n with
  | zero =>
    intro X h k hk
    rw [show X = [] from List.eq_nil_of_length_eq_zero (by omega), blocks_nil] at hk
    exact absurd hk (by simp)
  | succ g ih =>
    intro X h k hk i hi
    cases X with
    | nil => rw [blocks_nil] at hk; exact absurd hk (by simp)
    | cons c cs =>
      rw [blocks_cons c cs] at hk hi ⊢
      cases k with
      | zero => exact absurd hi (by simp)
      | succ j =>
        have hlenr : (peel (c.getD 0 0) cs).2.length ≤ g := by
          have := peel_len2 (c.getD 0 0) cs
          rw [List.length_cons] at h
          omega
        have hj : j < (blocks (peel (c.getD 0 0) cs).2).length := by
          rw [List.length_cons] at hk; omega
        have hB0 : BlkG (c :: (peel (c.getD 0 0) cs).1) := blocks_head_blkG c cs
        have hroot : ent ((blocks (peel (c.getD 0 0) cs).2).getD j []) 0 0 ≤ c.getD 0 0 := by
          have h1 := blocks_root_le g (peel (c.getD 0 0) cs).2 hlenr j hj
          have h2 : ent (peel (c.getD 0 0) cs).2 0 0 ≤ c.getD 0 0 := by
            refine peel_stop (c.getD 0 0) cs ?_
            rcases Nat.eq_or_lt_of_le (Nat.zero_le (peel (c.getD 0 0) cs).2.length) with he | he
            · exfalso
              rw [show (peel (c.getD 0 0) cs).2 = [] from
                List.eq_nil_of_length_eq_zero he.symm, blocks_nil] at hj
              exact absurd hj (by simp)
            · exact he
          omega
        show ent ((blocks (peel (c.getD 0 0) cs).2).getD j []) 0 0
          ≤ ent ((c :: (peel (c.getD 0 0) cs).1)
              ++ ((blocks (peel (c.getD 0 0) cs).2).take j).flatten) i 0
        rcases Nat.lt_or_ge i (c :: (peel (c.getD 0 0) cs).1).length with hlt | hge
        · rw [ent_append_left _ _ i 0 hlt]
          rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with hi0 | hi0
          · rw [← hi0]
            show _ ≤ c.getD 0 0
            omega
          · have := hB0.2 i hi0 hlt
            show _ ≤ ent (c :: (peel (c.getD 0 0) cs).1) i 0
            have hc : ent (c :: (peel (c.getD 0 0) cs).1) 0 0 = c.getD 0 0 := rfl
            omega
        · rw [ent_append _ _ i 0 hge]
          refine ih (peel (c.getD 0 0) cs).2 hlenr j hj _ ?_
          rw [List.take_succ_cons, List.flatten_cons, List.length_append] at hi
          omega

theorem len_le_flatten_lenG : ∀ (Bs : List Matrix), (∀ Bk ∈ Bs, BlkG Bk) →
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

theorem ppair_ofBlocks (Bs : List Matrix) (hb : ∀ Bk ∈ Bs, BlkG Bk)
    (hm : ∀ k, k < Bs.length → ∀ i, i < ((Bs.take k).flatten).length →
      ent (Bs.getD k []) 0 0 ≤ ent ((Bs.take k).flatten) i 0) :
    ppair (psM Bs.flatten) = Bs.map psM := by
  show ppairAux ((psM Bs.flatten).length + 1) (psM Bs.flatten)
    (lenI (psM Bs.flatten) - 1) [] = _
  rw [lenI_psM, show (psM Bs.flatten) = psM (Bs.flatten ++ []) from by rw [List.append_nil],
    ppairAux_blocksG _ Bs [] [] hb hm (by
      rw [List.append_nil, psM_len]
      exact Nat.le_trans (len_le_flatten_lenG Bs hb) (by omega))]
  simp

/-- **`ppair` は走る最小値で切ったブロック列。** -/
theorem ppair_blocksG (X : Matrix) : ppair (psM X) = (blocks X).map psM := by
  have hf : (blocks X).flatten = X := blocks_flatten X.length X (Nat.le_refl _)
  have h := ppair_ofBlocks (blocks X) (blocks_blkG X.length X (Nat.le_refl _))
    (blocks_min X.length X (Nat.le_refl _))
  rw [hf] at h
  exact h

/-- **`brF` は対角の後ろのブロック列。** -/
theorem brF_blocks (Mat : Matrix) (h : 0 < Mat.length) :
    brF (psM Mat) = (blocks (Mat.drop (runLen Mat + 1))).map psM := by
  show ppair ((psM Mat).drop (trMax (psM Mat) + 1).toNat) = _
  rw [trMax_runLen Mat h,
    show (((runLen Mat : Nat) : Int) + 1).toNat = runLen Mat + 1 from by omega,
    show (psM Mat).drop (runLen Mat + 1) = psM (Mat.drop (runLen Mat + 1)) from by
      show (Mat.map _).drop _ = (Mat.drop _).map _
      rw [List.map_drop],
    ppair_blocksG]

/-- 枝を連ねると対角の後ろになる。 -/
theorem brF_flatten (Mat : Matrix) (h : 0 < Mat.length) :
    (brF (psM Mat)).flatten = (psM Mat).drop (runLen Mat + 1) := by
  rw [brF_blocks Mat h, ← psM_flatten,
    blocks_flatten (Mat.drop (runLen Mat + 1)).length _ (Nat.le_refl _)]
  show (Mat.drop (runLen Mat + 1)).map _ = (Mat.map _).drop _
  rw [List.map_drop]

/-- **§25 の `hsplit`。** 対角と枝で領域の行列がちょうど割れる。 -/
theorem hsplit_matB (a : B) (hnf : nfLe 1 a = true) :
    jjSeq 0 ((runLen (matB (.nd 0 .nil a) 0) : Nat) : Int)
      ++ (brF (psM (matB (.nd 0 .nil a) 0))).flatten = psM (matB (.nd 0 .nil a) 0) := by
  have hne : (B.nd 0 .nil a) ≠ .nil := by intro h; exact B.noConfusion h
  have hpos : 0 < (matB (B.nd 0 .nil a) 0).length := matB_len_pos _ 0 hne
  rw [← take_jjSeq (matB (B.nd 0 .nil a) 0) (runLen (matB (B.nd 0 .nil a) 0))
      (runLen_lt _ hpos) (spine_diag_matB a hnf),
    brF_flatten _ hpos, psM_split]

end

/-! ## §31 SAY IT ABOUT MATRICES, NOT ABOUT TREES

`hterm` is the last hypothesis of §25, and its recursive call is `red` OF A BRANCH.  Stated
about `matB`, that call needs each branch to be `matB` of a SUBTREE — a fact about `decodeB`
that nothing here has, and the one place where the tree would come back after §30 got rid of
it.  So the statement moves to where the proof already lives.

Everything §27 and §28 proved about `matB` is two properties of a matrix:

    StepOK X : ent X (j+1) 0 ≤ ent X j 0 + 1                     the preorder
    LvlOK X  : k the tree parent of i → ent X i 1 ≤ ent X k 1 + 1  the normal form

`NFM` is their conjunction, `matB` of a normal-form index satisfies it (`nfm_matB`), and —
this is the point — it is inherited by `take`, by `drop`, and hence by every block
(`nfm_blocks`).  A branch of an `NFM` matrix is an `NFM` matrix, with no tree in sight.

The goal restated: `red` moves each top-level block so that its root's DEPTH equals its
root's LEVEL, and leaves everything else where it is.

    shiftToLvl X = incrFirst (psM X) (gp1 (psM X) 0 - gp0 (psM X) 0)
    canonM X     = ((blocks X).map shiftToLvl).flatten

`canonM (matB s d) = canon s` on §20's population at four depths, so this is §20's identity
said differently, not a different identity. -/

section
open Trans.Recal

/-- 深さは 1 列で高々 1 しか増えない (§27 の `matB_step_depth` を行列の性質として)。 -/
def StepOK (X : Matrix) : Prop := ∀ j, ent X (j + 1) 0 ≤ ent X j 0 + 1

/-- 段は木の親の段 + 1 以下 (§28 の `matB_lvl_le_par` を行列の性質として)。 -/
def LvlOK (X : Matrix) : Prop :=
  ∀ k i, LMin X k i → ent X k 0 + 1 = ent X i 0 → ent X i 1 ≤ ent X k 1 + 1

/-- **標準形の行列。** `matB` の標準形の添字はこれを満たし、部分行列も満たす。 -/
def NFM (X : Matrix) : Prop := StepOK X ∧ LvlOK X

theorem nfm_matB (t : B) (m d : Nat) (hnf : nfLe m t = true) : NFM (matB t d) :=
  ⟨fun j => matB_step_depth t d j, fun k i hlm hd => matB_lvl_le_par t m d hnf k i hlm hd⟩

/-! ### 部分行列 -/

theorem ent_drop (X : Matrix) (n j y : Nat) : ent (X.drop n) j y = ent X (n + j) y := by
  show ((X.drop n).getD j []).getD y 0 = ((X.getD (n + j) [])).getD y 0
  rw [show (X.drop n).getD j [] = X.getD (n + j) [] from by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]]

theorem ent_take (X : Matrix) (n j y : Nat) (h : j < n) : ent (X.take n) j y = ent X j y := by
  show ((X.take n).getD j []).getD y 0 = ((X.getD j [])).getD y 0
  rw [show (X.take n).getD j [] = X.getD j [] from by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]]

theorem stepOK_drop (X : Matrix) (n : Nat) (h : StepOK X) : StepOK (X.drop n) := by
  intro j
  rw [ent_drop, ent_drop, show n + (j + 1) = (n + j) + 1 from by omega]
  exact h (n + j)

theorem stepOK_take (X : Matrix) (n : Nat) (h : StepOK X) : StepOK (X.take n) := by
  intro j
  rcases Nat.lt_or_ge (j + 1) n with hj | hj
  · rw [ent_take X n (j + 1) 0 hj, ent_take X n j 0 (by omega)]
    exact h j
  · rw [ent_oob _ (j + 1) 0 (by
      rw [List.length_take]
      omega)]
    omega

theorem lmin_drop (X : Matrix) (n k i : Nat) (h : LMin (X.drop n) k i) : LMin X (n + k) (n + i) := by
  refine ⟨by have := h.1; omega, ?_⟩
  intro p hp1 hp2
  have := h.2 (p - n) (by omega) (by omega)
  rw [ent_drop, ent_drop, show n + (p - n) = p from by omega] at this
  exact this

theorem lvlOK_drop (X : Matrix) (n : Nat) (h : LvlOK X) : LvlOK (X.drop n) := by
  intro k i hlm hd
  rw [ent_drop, ent_drop] at hd ⊢
  exact h (n + k) (n + i) (lmin_drop X n k i hlm) hd

theorem lmin_take (X : Matrix) (n k i : Nat) (hi : i < n) (h : LMin (X.take n) k i) :
    LMin X k i := by
  refine ⟨h.1, ?_⟩
  intro p hp1 hp2
  have := h.2 p hp1 hp2
  rw [ent_take X n k 0 (by have := h.1; omega), ent_take X n p 0 (by omega)] at this
  exact this

theorem lvlOK_take (X : Matrix) (n : Nat) (h : LvlOK X) : LvlOK (X.take n) := by
  intro k i hlm hd
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [ent_take X n i 1 hi, ent_take X n k 1 (by have := hlm.1; omega)]
    rw [ent_take X n i 0 hi, ent_take X n k 0 (by have := hlm.1; omega)] at hd
    exact h k i (lmin_take X n k i hi hlm) hd
  · rw [ent_oob _ i 1 (by rw [List.length_take]; omega)]
    omega

theorem nfm_drop (X : Matrix) (n : Nat) (h : NFM X) : NFM (X.drop n) :=
  ⟨stepOK_drop X n h.1, lvlOK_drop X n h.2⟩

theorem nfm_take (X : Matrix) (n : Nat) (h : NFM X) : NFM (X.take n) :=
  ⟨stepOK_take X n h.1, lvlOK_take X n h.2⟩

/-- ブロックは部分行列なので標準形を保つ。 -/
theorem nfm_blocks : ∀ (n : Nat) (X : Matrix), X.length ≤ n → NFM X → ∀ Bk ∈ blocks X, NFM Bk := by
  intro n
  induction n with
  | zero =>
    intro X h _ Bk hBk
    rw [show X = [] from List.eq_nil_of_length_eq_zero (by omega), blocks_nil] at hBk
    exact absurd hBk (by simp)
  | succ g ih =>
    intro X h hnf Bk hBk
    cases X with
    | nil => rw [blocks_nil] at hBk; exact absurd hBk (by simp)
    | cons c cs =>
      rw [blocks_cons c cs] at hBk
      rcases List.mem_cons.mp hBk with rfl | hBk
      · have hpre : c :: (peel (c.getD 0 0) cs).1
            = (c :: cs).take (c :: (peel (c.getD 0 0) cs).1).length := by
          have := peel_append (c.getD 0 0) cs
          rw [show c :: cs = (c :: (peel (c.getD 0 0) cs).1) ++ (peel (c.getD 0 0) cs).2 from by
            show c :: cs = c :: ((peel (c.getD 0 0) cs).1 ++ (peel (c.getD 0 0) cs).2)
            rw [this]]
          rw [List.take_left]
        rw [hpre]
        exact nfm_take _ _ hnf
      · refine ih (peel (c.getD 0 0) cs).2 ?_ ?_ Bk hBk
        · have := peel_len2 (c.getD 0 0) cs
          rw [List.length_cons] at h
          omega
        · have hsuf : (peel (c.getD 0 0) cs).2
              = (c :: cs).drop (c :: (peel (c.getD 0 0) cs).1).length := by
            have := peel_append (c.getD 0 0) cs
            rw [show c :: cs = (c :: (peel (c.getD 0 0) cs).1) ++ (peel (c.getD 0 0) cs).2 from by
              show c :: cs = c :: ((peel (c.getD 0 0) cs).1 ++ (peel (c.getD 0 0) cs).2)
              rw [this]]
            rw [List.drop_left]
          rw [hsuf]
          exact nfm_drop _ _ hnf

/-! ### 言い直した目標 -/

/-- ブロック 1 つを「根の深さ = 根の段」の位置へ動かしたもの。 -/
def shiftToLvl (X : Matrix) : PS := incrFirst (psM X) (gp1 (psM X) 0 - gp0 (psM X) 0)

/-- 行列を各ブロックごとに動かしたもの — `red` が返すはずの形。 -/
def canonM (X : Matrix) : PS := ((blocks X).map shiftToLvl).flatten

-- §20 の `canon` と同じもの (母集団で確認)。
#guard (enumFree 3 4).all fun s => (List.range 4).all fun d => canonM (matB s d) == canon s
#guard (enumFree 3 4).all fun s => (List.range 4).all fun d =>
  redP (psM (matB s d)) == canonM (matB s d)

end

/-! ## §32 WHY THE REBUILD GIVES THE BRANCH BACK

§23 measured `(jnJ + 1, nJ + 1) :: derp bJ = bJ` at 467 of 467 and called it the crux.  This
proves the column identity behind it: for a branch root at index `s`, depth `dq`, level `u`,
hanging off the diagonal,

    fpar M 0 s 0 + 1 = dq        and        (nJ of s) + 1 = u

so `(jnJ + 1, nJ + 1)` IS the branch root's own column.  Two walks, and both are short because
the diagonal is a diagonal.

ROW 0.  The scan for the parent goes left from `s - 1`.  Everything between the diagonal and
`s` belongs to earlier branches and is at least as deep as `dq` (the running-minimum property
of §30's `blocks`, taken as a hypothesis here), so nothing there is a candidate; on the
diagonal the depths are `0, 1, 2, …`, so the first candidate is column `dq - 1`
(`fpar0Aux_skip`, `fpar0_blockroot`).

ROW 1.  From there the walk follows the row-0 chain, which on the diagonal is just `j ↦ j - 1`
(`fpar0_spine`), and stops at the first column whose LEVEL is below `u`.  On the diagonal
index = level, so that is column `u - 1` — provided `u ≤ dq`, which is exactly §28's
`lvl_le_fpar` at the joint (`fpar1Aux_spine`, `fpar_one_spine`).  When `u = 0` the algorithm
takes its own `-1` branch and `nJ + 1 = 0 = u` holds too, so `rebuild_col` needs no case
split at the end.

`hmid` — "everything between the diagonal and `s` is at least as deep as `dq`" — is the one
hypothesis still to be discharged from §30's block decomposition. -/

section
open Trans.Recal

/-- 左へ走査して、途中に候補が無ければ `q` で当たる。 -/
theorem fpar0Aux_skip (M : Matrix) (tgt : Nat) : ∀ (f i q : Nat), q ≤ i →
    (∀ p, q < p → p ≤ i → ¬(ent M p 0 < tgt)) → ent M q 0 < tgt → i - q < f →
    fpar0Aux f (psM M) ((tgt : Nat) : Int) ((i : Nat) : Int) 0 = ((q : Nat) : Int) := by
  intro f
  induction f with
  | zero => intro i q _ _ _ h; exact absurd h (by omega)
  | succ g ih =>
    intro i q h1 h2 h3 h4
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact fpar0Aux_hit _ _ _ _ _ (by omega) (by rw [psM_gp0]; omega)
    · show (if ((i : Nat) : Int) < 0 then (-1 : Int)
            else if gp0 (psM M) ((i : Nat) : Int) < ((tgt : Nat) : Int) then ((i : Nat) : Int)
            else fpar0Aux g (psM M) ((tgt : Nat) : Int) (((i : Nat) : Int) - 1) 0) = _
      rw [if_neg (by omega), psM_gp0,
        if_neg (by have := h2 i (by omega) (by omega); omega),
        show ((i : Nat) : Int) - 1 = ((i - 1 : Nat) : Int) from by omega]
      exact ih (i - 1) q (by omega) (fun p hp1 hp2 => h2 p hp1 (by omega)) h3 (by omega)

/-- **対角にぶら下がるブロックの根の行 0 の親は、対角の 1 つ浅い列。** -/
theorem fpar0_blockroot (M : Matrix) (tr dq s : Nat)
    (hcol : ∀ j, j ≤ tr → ent M j 0 = j ∧ ent M j 1 = j)
    (hdq : 1 ≤ dq) (hdqtr : dq ≤ tr + 1) (hs : tr < s) (hslen : s < M.length)
    (hdep : ent M s 0 = dq)
    (hmid : ∀ p, tr < p → p < s → dq ≤ ent M p 0) :
    fpar0 (psM M) ((s : Nat) : Int) 0 = ((dq - 1 : Nat) : Int) := by
  rw [fpar0_in _ _ _ (by rw [lenI_psM]; omega), psM_gp0, hdep,
    show ((s : Nat) : Int) - 1 = ((s - 1 : Nat) : Int) from by omega]
  refine fpar0Aux_skip M dq _ (s - 1) (dq - 1) (by omega) ?_ ?_ (by rw [psM_len]; omega)
  · intro p hp1 hp2
    rcases Nat.lt_or_ge tr p with hp | hp
    · have := hmid p hp (by omega)
      omega
    · have := (hcol p hp).1
      omega
  · have := (hcol (dq - 1) (by omega)).1
    omega

/-- 対角の上では行 0 の親は 1 つ左。 -/
theorem fpar0_spine (M : Matrix) (tr : Nat)
    (hcol : ∀ j, j ≤ tr → ent M j 0 = j ∧ ent M j 1 = j)
    (j : Nat) (hj : 1 ≤ j) (hjtr : j ≤ tr) (hlen : j < M.length) :
    fpar0 (psM M) ((j : Nat) : Int) 0 = ((j - 1 : Nat) : Int) := by
  rw [fpar0_in _ _ _ (by rw [lenI_psM]; omega), psM_gp0,
    show ((j : Nat) : Int) - 1 = ((j - 1 : Nat) : Int) from by omega]
  refine fpar0Aux_hit _ _ _ _ _ (by omega) ?_
  rw [psM_gp0, (hcol (j - 1) (by omega)).1, (hcol j hjtr).1]
  omega

/-- 対角を下りると、段が `u` 未満の最初の列は添字 `u-1`。 -/
theorem fpar1Aux_spine (M : Matrix) (tr u : Nat)
    (hcol : ∀ j, j ≤ tr → ent M j 0 = j ∧ ent M j 1 = j)
    (hu : 1 ≤ u) (htr : tr < M.length) :
    ∀ (f q : Nat), u ≤ q → q ≤ tr → q - u < f →
      fpar1Aux f (psM M) ((u : Nat) : Int) ((q : Nat) : Int) 0 = ((u - 1 : Nat) : Int) := by
  intro f
  induction f with
  | zero => intro q _ _ h; exact absurd h (by omega)
  | succ g ih =>
    intro q h1 h2 h3
    have hpar : fpar0 (psM M) ((q : Nat) : Int) 0 = ((q - 1 : Nat) : Int) :=
      fpar0_spine M tr hcol q (by omega) h2 (by omega)
    show (let z := fpar0 (psM M) ((q : Nat) : Int) 0
          if z < 0 then (-1 : Int)
          else if gp1 (psM M) z < ((u : Nat) : Int) then z
          else fpar1Aux g (psM M) ((u : Nat) : Int) z 0) = _
    rw [hpar, if_neg (by omega), psM_gp1, (hcol (q - 1) (by omega)).2]
    by_cases hq : q = u
    · rw [if_pos (by omega), hq]
    · rw [if_neg (by omega)]
      exact ih (q - 1) (by omega) (by omega) (by omega)

/-- **対角にぶら下がる列の行 1 の親は、その段の 1 つ下の対角の列。** -/
theorem fpar_one_spine (M : Matrix) (tr u p x : Nat)
    (hcol : ∀ j, j ≤ tr → ent M j 0 = j ∧ ent M j 1 = j)
    (hu : 1 ≤ u) (htr : tr < M.length) (hx : x < M.length)
    (hpar : fpar0 (psM M) ((x : Nat) : Int) 0 = ((p : Nat) : Int))
    (hptr : p ≤ tr) (hup : u ≤ p + 1) (hlvl : ent M x 1 = u) :
    fpar (psM M) 1 ((x : Nat) : Int) 0 = ((u - 1 : Nat) : Int) := by
  rw [Rows.Ladder.fpar1_unfold _ _ _ (by rw [lenI_psM]; omega), psM_gp1, hlvl]
  show (let z := fpar0 (psM M) ((x : Nat) : Int) 0
        if z < 0 then (-1 : Int)
        else if gp1 (psM M) z < ((u : Nat) : Int) then z
        else fpar1Aux (psM M).length (psM M) ((u : Nat) : Int) z 0) = _
  rw [hpar, if_neg (by omega), psM_gp1, (hcol p hptr).2]
  by_cases hp : p < u
  · rw [if_pos (by omega)]
    have : p = u - 1 := by omega
    rw [this]
  · rw [if_neg (by omega)]
    refine fpar1Aux_spine M tr u hcol hu htr (psM M).length p (by omega) hptr ?_
    rw [psM_len]
    omega

/-- **§23 の測った恒等式の中身。** 継ぎ目 +1 は枝の根の深さ、行 1 の親 +1 はその段。 -/
theorem rebuild_col (M : Matrix) (tr dq u s : Nat)
    (hcol : ∀ j, j ≤ tr → ent M j 0 = j ∧ ent M j 1 = j)
    (hdq : 1 ≤ dq) (hdqtr : dq ≤ tr + 1) (hs : tr < s) (hslen : s < M.length)
    (htr : tr < M.length)
    (hdep : ent M s 0 = dq) (hlvl : ent M s 1 = u) (hudq : u ≤ dq)
    (hmid : ∀ p, tr < p → p < s → dq ≤ ent M p 0) :
    fpar (psM M) 0 ((s : Nat) : Int) 0 + 1 = ((dq : Nat) : Int)
    ∧ (if (((u : Nat) : Int) == 0) then (-1 : Int)
       else fpar (psM M) 1 ((s : Nat) : Int) 0) + 1 = ((u : Nat) : Int) := by
  have hp0 : fpar0 (psM M) ((s : Nat) : Int) 0 = ((dq - 1 : Nat) : Int) :=
    fpar0_blockroot M tr dq s hcol hdq hdqtr hs hslen hdep hmid
  constructor
  · rw [fpar_zero, hp0]
    omega
  · cases u with
    | zero =>
      rw [if_pos (show ((((0 : Nat)) : Int) == 0) = true from rfl)]
      omega
    | succ w =>
      rw [show ((((w + 1 : Nat)) : Int) == 0) = false from decide_eq_false (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [fpar_one_spine M tr (w + 1) (dq - 1) s hcol (by omega) htr hslen hp0
        (by omega) (by omega) hlvl]
      omega

end

/-! ## §33 `hmid`, AND WHERE THE BRANCHES START

§32 left one hypothesis undischarged — that everything between the diagonal and a branch root
is at least as deep as that root — and needed two indices it did not compute.  Both come out
of §30.

`hmid_of_blocks` is §30's `blocks_min` moved from the suffix's indexing to the matrix's: the
columns before block `J` are `((blocks X).take J).flatten`, which is a PREFIX of `X`
(`ent_take_flatten`), and `X` is `M.drop (tr+1)` (`ent_drop`).  Nothing new is proved; the
running minimum was already there.

`firstNodes` and `joints` are then arithmetic.  `idxSum` is the list of partial sums of the
branch lengths — `idxSum_fold` says so in closed form, by the one induction that unwinds the
`foldl` — hence

    firstNodes M .getD J = trMax M + 1 + (length of the branches before J)
    joints M     .getD J = fpar M 0 (that) 0

which is exactly the pair `rebuild_col` consumes: the first is the branch root's index in `M`,
the second is its row-0 parent.

With these the fold's `J`-th term is pinned to `bJ` for every `J`, and what is left of the
whole `red` proof is putting the induction together. -/

section
open Trans.Recal

/-- ブロック列の先頭 `J` 個を連ねたものは全体の接頭辞。 -/
theorem take_flatten_prefix (Bs : List Matrix) (J : Nat) :
    (Bs.take J).flatten ++ (Bs.drop J).flatten = Bs.flatten := by
  rw [← List.flatten_append, List.take_append_drop]

theorem ent_take_flatten (Bs : List Matrix) (J i : Nat)
    (hi : i < ((Bs.take J).flatten).length) :
    ent ((Bs.take J).flatten) i 0 = ent Bs.flatten i 0 := by
  rw [← take_flatten_prefix Bs J, ent_append_left _ _ i 0 hi]

/-- **`hmid`。** 対角と枝の間はすべてその枝の根より深い。 -/
theorem hmid_of_blocks (M : Matrix) (tr J : Nat)
    (hJ : J < (blocks (M.drop (tr + 1))).length) :
    ∀ p, tr < p →
      p < tr + 1 + (((blocks (M.drop (tr + 1))).take J).flatten).length →
      ent ((blocks (M.drop (tr + 1))).getD J []) 0 0 ≤ ent M p 0 := by
  intro p hp1 hp2
  obtain ⟨i, rfl⟩ : ∃ i, p = tr + 1 + i := ⟨p - (tr + 1), by omega⟩
  have hi : i < (((blocks (M.drop (tr + 1))).take J).flatten).length := by omega
  have hbf : ent (((blocks (M.drop (tr + 1))).take J).flatten) i 0
      = ent (M.drop (tr + 1)) i 0 := by
    rw [ent_take_flatten _ J i hi,
      blocks_flatten (M.drop (tr + 1)).length (M.drop (tr + 1)) (Nat.le_refl _)]
  rw [show ent M (tr + 1 + i) 0 = ent (M.drop (tr + 1)) i 0 from (ent_drop M (tr + 1) i 0).symm,
    ← hbf]
  exact blocks_min (M.drop (tr + 1)).length (M.drop (tr + 1)) (Nat.le_refl _) J hJ i hi

/-! ### `idxSum` は部分和 -/

theorem idxSum_fold : ∀ (Q : List PS) (acc : List Int) (s : Int),
    (Q.foldl (fun (a : List Int × Int) q => (a.1 ++ [a.2 + (q.length : Int)],
        a.2 + (q.length : Int))) (acc, s)).1
      = acc ++ (List.range Q.length).map
          (fun J => s + ((((Q.take (J + 1)).flatten).length : Nat) : Int)) := by
  intro Q
  induction Q with
  | nil => intro acc s; show acc = acc ++ []; rw [List.append_nil]
  | cons q qs ih =>
    intro acc s
    show (qs.foldl _ (acc ++ [s + (q.length : Int)], s + (q.length : Int))).1 = _
    rw [ih (acc ++ [s + (q.length : Int)]) (s + (q.length : Int)), List.append_assoc]
    refine congrArg (acc ++ ·) ?_
    show [s + (q.length : Int)] ++ (List.range qs.length).map
        (fun J => s + (q.length : Int) + ((((qs.take (J + 1)).flatten).length : Nat) : Int))
      = (List.range (qs.length + 1)).map
        (fun J => s + (((((q :: qs).take (J + 1)).flatten).length : Nat) : Int))
    have ht : ∀ J : Nat, s + (q.length : Int)
        + ((((qs.take (J + 1)).flatten).length : Nat) : Int)
        = s + (((((q :: qs).take (J + 1 + 1)).flatten).length : Nat) : Int) := by
      intro J
      rw [show ((q :: qs).take (J + 1 + 1)).flatten = q ++ (qs.take (J + 1)).flatten from by
        rw [List.take_succ_cons, List.flatten_cons], List.length_append]
      omega
    have hh : ((((q :: qs).take (0 + 1)).flatten).length : Nat) = q.length := by simp
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hh]
    refine congrArg (fun l => (s + (q.length : Int)) :: l) ?_
    exact List.map_congr_left (fun J _ => ht J)

theorem idxSum_getD (Q : List PS) (J : Nat) (hJ : J ≤ Q.length) :
    (idxSum Q).getD J 0 = ((((Q.take J).flatten).length : Nat) : Int) := by
  show ((Q.foldl _ ([0], 0)).1).getD J 0 = _
  rw [idxSum_fold Q [0] 0]
  cases J with
  | zero => rfl
  | succ k =>
    rw [getD_app_right _ _ _ (k + 1) (by simp),
      show (k + 1) - ([(0 : Int)]).length = k from by simp]
    rw [show ((List.range Q.length).map
        (fun J => (0 : Int) + ((((Q.take (J + 1)).flatten).length : Nat) : Int))).getD k 0
      = (0 : Int) + ((((Q.take (k + 1)).flatten).length : Nat) : Int) from
        getD_map_range Q.length _ 0 k (by omega)]
    omega

theorem getD_map_lt {α β : Type _} (f : α → β) (l : List α) (da : α) (db : β) (J : Nat)
    (h : J < l.length) : (l.map f).getD J db = f (l.getD J da) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    show l[J]? = some l[J] from List.getElem?_eq_getElem h]
  rfl

theorem getD_dropLast {α : Type _} (l : List α) (d : α) (J : Nat) (h : J + 1 < l.length) :
    l.dropLast.getD J d = l.getD J d := by
  rw [List.dropLast_eq_take, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (by omega)]

theorem idxSum_length (Q : List PS) : (idxSum Q).length = Q.length + 1 := by
  show ((Q.foldl (fun (a : List Int × Int) q => (a.1 ++ [a.2 + (q.length : Int)],
      a.2 + (q.length : Int))) ([0], 0)).1).length = _
  rw [idxSum_fold Q [0] 0, List.length_append, List.length_map, List.length_range]
  simp
  omega

theorem firstNodes_length (M : PS) : (firstNodes M).length = (brF M).length + 1 := by
  show ((idxSum (brF M)).map _).length = _
  rw [List.length_map, idxSum_length]

/-- **`firstNodes` の `J` 番目は `J` 番目の枝が始まる添字。** -/
theorem firstNodes_getD (M : PS) (J : Nat) (hJ : J ≤ (brF M).length) :
    (firstNodes M).getD J 0
      = trMax M + 1 + ((((brF M).take J).flatten).length : Int) := by
  show ((idxSum (brF M)).map (fun e => trMax M + 1 + e)).getD J 0 = _
  rw [getD_map_lt _ _ (0 : Int) (0 : Int) J (by rw [idxSum_length]; omega),
    idxSum_getD _ J hJ]

/-- **`joints` の `J` 番目はその枝の根の行 0 の親。** -/
theorem joints_getD (M : PS) (J : Nat) (hJ : J < (brF M).length) :
    (joints M).getD J 0 = fpar M 0 ((firstNodes M).getD J 0) 0 := by
  show ((firstNodes M).dropLast.map (fun e => fpar M 0 e 0)).getD J 0 = _
  rw [getD_map_lt _ _ (0 : Int) (0 : Int) J (by
      rw [List.length_dropLast, firstNodes_length]
      omega),
    getD_dropLast _ _ J (by rw [firstNodes_length]; omega)]

end

/-! ## §34 THE INDUCTION, STARTED

§31 said the goal as `red (psM X) = canonM X` for `NFM X`.  The induction is on `X.length`,
and it splits the way `red` itself does: nothing, several blocks, one block.

    redM_nil : red f (psM []) = canonM []
    redM_sum : (each block already known) → red (f+1) (psM X) = canonM X   [X not principal]

`redM_sum` is the `ppair` branch and needs nothing new — §30's `ppair_blocksG` turns it into
the induction hypothesis applied block by block, and a block of a several-block matrix is
strictly shorter, so the recursion is well founded on length.

The one-block case has to know that `canonM` says nothing extra there: `peel` swallows the
whole tail when every column is deeper than the head, so `blocks X = [X]` and
`canonM X = shiftToLvl X` (`blocks_single`, `canonM_single`).  That is what lets the two
statements — "each block moves to its own level" and "the matrix moves to its level" — be the
same theorem.

WHAT IS LEFT is the one-block case itself, which is where `red` actually computes: `isZeroP`,
then a root of level 0 at depth 0 (the fold, §25 with §32/§33's hypotheses), then a root of
level 0 deeper down (one `red_shift`), then a root of level ≥ 1 (`red_head_pos`, which
prepends a diagonal and lands back in the fold).  Only the fold recurses, and it recurses into
BRANCHES — shorter than `X` — so the same measure carries it. -/

section
open Trans.Recal

theorem peel_all : ∀ (dd : Nat) (X : Matrix), (∀ i, i < X.length → dd < ent X i 0) →
    peel dd X = (X, []) := by
  intro dd X
  induction X with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    have hc : dd < c.getD 0 0 := h 0 (by simp)
    rw [peel_cons_pos dd c cs hc,
      ih (fun i hi => by
        have := h (i + 1) (by simp; omega)
        exact this)]

/-- ブロック 1 つの行列のブロック列は自分だけ。 -/
theorem blocks_single (X : Matrix) (h : BlkG X) : blocks X = [X] := by
  cases X with
  | nil => exact absurd h.1 (by simp)
  | cons c cs =>
    have hall : ∀ i, i < cs.length → c.getD 0 0 < ent cs i 0 := by
      intro i hi
      have := h.2 (i + 1) (by omega) (by simp; omega)
      exact this
    rw [blocks_cons c cs, peel_all (c.getD 0 0) cs hall, blocks_nil]

theorem canonM_single (X : Matrix) (h : BlkG X) : canonM X = shiftToLvl X := by
  show ((blocks X).map shiftToLvl).flatten = _
  rw [blocks_single X h]
  show shiftToLvl X ++ [] = _
  rw [List.append_nil]

/-! ### 場合分けの 2 つ -/

theorem redM_nil (f : Nat) : red f (psM ([] : Matrix)) = canonM [] := by
  show red f ([] : PS) = _
  cases f with
  | zero =>
    rw [show canonM [] = [] from by
      show ((blocks []).map _).flatten = _
      rw [blocks_nil]
      rfl]
    rfl
  | succ g =>
    rw [red_nonprin [] g (by decide) (by decide), show ppair ([] : PS) = [] from by decide,
      show canonM [] = [] from by show ((blocks []).map _).flatten = _; rw [blocks_nil]; rfl]
    rfl

/-- 最上位のブロックが 2 つ以上の場合。 -/
theorem redM_sum (f : Nat) (X : Matrix) (hzero : isZeroP (psM X) = false)
    (hprin : isPrincipalP (psM X) = false)
    (ih : ∀ Bk ∈ blocks X, red f (psM Bk) = shiftToLvl Bk) :
    red (f + 1) (psM X) = canonM X := by
  rw [red_nonprin _ f hzero hprin, ppair_blocksG, List.flatMap_map]
  show ((blocks X).map (fun Bk => red f (psM Bk))).flatten = _
  rw [List.map_congr_left ih]
  rfl

end

/-! ## §35 THE LEVEL-POSITIVE CASE NEEDS A LOOSER SPINE

The one-block case splits four ways, and three are short.  The fourth — a root of LEVEL ≥ 1 —
sends `red` through `red_head_pos`, which prepends a diagonal and pushes the block out:

    auxA X = jjSeq 0 (u-1) ++ incrFirst (psM X) u

and MEASURED (278 indices × 3 depths), its reduct is

    red (auxA X) = jjSeq 0 (u-1) ++ shiftToLvl X

which is exactly what the surrounding dance needs.  **But `auxA X` is not one of §31's
matrices.**  Its root is `(0,0)` and its levels still run `0, 1, 2, …`, yet at the junction the
DEPTH jumps from `u-1` to `d+u`, so `StepOK` fails and §27's diagonal argument does not apply
— the third guard below records that `trMax` does not stop where a diagonal would.

What survives is what the two searches actually use.  `fpar0` on the spine only needs the
spine's DEPTHS TO INCREASE, not to equal the index (`fpar0_spine'`); and `fpar1`'s stopping
test only reads LEVELS, which do equal the index (`fpar1Aux_spine'`, `fpar_one_spine'`).  So
the primed lemmas replace §32's, with "depth = index" weakened to "depth increases" and
"level = index" kept.

`red_fold_to` is the matching generalisation of §25's `red_fold_id`: it drops the requirement
that each fold term give its own branch back, and concludes `jjSeq 0 tr ++ cs.flatten` for
whatever the terms are.  On a diagonal-rooted matrix the terms ARE the branches and one
recovers §25; on `auxA X` they are the branches re-rooted, which is the point. -/

section
open Trans.Recal

/-- **畳み込みは対角のあとに各項を並べる。** 各項が何であるかは問わない版。 -/
theorem red_fold_to (M : PS) (f : Nat) (tr : Int) (cs : List PS)
    (hzero : isZeroP M = false) (hprin : isPrincipalP M = true)
    (hg0 : gp0 M 0 = 0) (hg1 : gp1 M 0 = 0)
    (htr : trMax M = tr) (hne : (tr == lenI M - 1) = false)
    (hlen : (brF M).length = cs.length)
    (hterm : ∀ J, J < cs.length →
      incrFirst (red f (((joints M).getD J 0 + 1,
          (if gp1 ((brF M).getD J []) 0 == 0 then (-1 : Int)
           else fpar M 1 ((firstNodes M).getD J 0) 0) + 1) :: derp ((brF M).getD J [])))
        ((joints M).getD J 0 - (if gp1 ((brF M).getD J []) 0 == 0 then (-1 : Int)
           else fpar M 1 ((firstNodes M).getD J 0) 0)) = cs.getD J []) :
    red (f + 1) M = jjSeq 0 tr ++ cs.flatten := by
  rw [Rows.Ladder.red_fold_open M f tr hzero hprin hg0 hg1 htr hne, hlen]
  show (List.range cs.length).foldl (fun r J => r ++
      incrFirst (red f (((joints M).getD J 0 + 1,
          (if gp1 ((brF M).getD J []) 0 == 0 then (-1 : Int)
           else fpar M 1 ((firstNodes M).getD J 0) 0) + 1) :: derp ((brF M).getD J [])))
        ((joints M).getD J 0 - (if gp1 ((brF M).getD J []) 0 == 0 then (-1 : Int)
           else fpar M 1 ((firstNodes M).getD J 0) 0)))
      (jjSeq 0 tr) = _
  rw [fold_to_flatten _ cs (jjSeq 0 tr) hterm]

/-- 対角の深さが真に増えていれば行 0 の親は 1 つ左 — 深さが添字と等しくなくてよい。 -/
theorem fpar0_spine' (M : Matrix) (tr : Nat)
    (hdep : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0)
    (j : Nat) (hj : 1 ≤ j) (hjtr : j ≤ tr) (hlen : j < M.length) :
    fpar0 (psM M) ((j : Nat) : Int) 0 = ((j - 1 : Nat) : Int) := by
  rw [fpar0_in _ _ _ (by rw [lenI_psM]; omega), psM_gp0,
    show ((j : Nat) : Int) - 1 = ((j - 1 : Nat) : Int) from by omega]
  refine fpar0Aux_hit _ _ _ _ _ (by omega) ?_
  rw [psM_gp0]
  have := hdep (j - 1) (by omega)
  rw [show j - 1 + 1 = j from by omega] at this
  omega

/-- 段が添字と等しい対角を下りると、段が `u` 未満の最初の列は添字 `u-1`。 -/
theorem fpar1Aux_spine' (M : Matrix) (tr u : Nat)
    (hdep : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0)
    (hlvl : ∀ j, j ≤ tr → ent M j 1 = j)
    (hu : 1 ≤ u) (htr : tr < M.length) :
    ∀ (f q : Nat), u ≤ q → q ≤ tr → q - u < f →
      fpar1Aux f (psM M) ((u : Nat) : Int) ((q : Nat) : Int) 0 = ((u - 1 : Nat) : Int) := by
  intro f
  induction f with
  | zero => intro q _ _ h; exact absurd h (by omega)
  | succ g ih =>
    intro q h1 h2 h3
    have hpar : fpar0 (psM M) ((q : Nat) : Int) 0 = ((q - 1 : Nat) : Int) :=
      fpar0_spine' M tr hdep q (by omega) h2 (by omega)
    show (let z := fpar0 (psM M) ((q : Nat) : Int) 0
          if z < 0 then (-1 : Int)
          else if gp1 (psM M) z < ((u : Nat) : Int) then z
          else fpar1Aux g (psM M) ((u : Nat) : Int) z 0) = _
    rw [hpar, if_neg (by omega), psM_gp1, hlvl (q - 1) (by omega)]
    by_cases hq : q = u
    · rw [if_pos (by omega), hq]
    · rw [if_neg (by omega)]
      exact ih (q - 1) (by omega) (by omega) (by omega)

/-- **段が添字と等しい対角にぶら下がる列の行 1 の親は、その段の 1 つ下の列。** -/
theorem fpar_one_spine' (M : Matrix) (tr u p x : Nat)
    (hdep : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0)
    (hlvl : ∀ j, j ≤ tr → ent M j 1 = j)
    (hu : 1 ≤ u) (htr : tr < M.length) (hx : x < M.length)
    (hpar : fpar0 (psM M) ((x : Nat) : Int) 0 = ((p : Nat) : Int))
    (hptr : p ≤ tr) (hup : u ≤ p + 1) (hlvlx : ent M x 1 = u) :
    fpar (psM M) 1 ((x : Nat) : Int) 0 = ((u - 1 : Nat) : Int) := by
  rw [Rows.Ladder.fpar1_unfold _ _ _ (by rw [lenI_psM]; omega), psM_gp1, hlvlx]
  show (let z := fpar0 (psM M) ((x : Nat) : Int) 0
        if z < 0 then (-1 : Int)
        else if gp1 (psM M) z < ((u : Nat) : Int) then z
        else fpar1Aux (psM M).length (psM M) ((u : Nat) : Int) z 0) = _
  rw [hpar, if_neg (by omega), psM_gp1, hlvl p hptr]
  by_cases hp : p < u
  · rw [if_pos (by omega)]
    have : p = u - 1 := by omega
    rw [this]
  · rw [if_neg (by omega)]
    refine fpar1Aux_spine' M tr u hdep hlvl hu htr (psM M).length p (by omega) hptr ?_
    rw [psM_len]
    omega

/-! ### 段が 1 以上の場合に `red` が作る行列 -/

/-- `red_head_pos` が作る行列: 対角を前置きして押し出したもの。 -/
def auxA (X : Matrix) : PS :=
  jjSeq 0 (gp1 (psM X) 0 - 1) ++ incrFirst (psM X) (gp1 (psM X) 0)

/-- その `red` の値 (測定)。 -/
def auxTarget (X : Matrix) : PS := jjSeq 0 (gp1 (psM X) 0 - 1) ++ shiftToLvl X

/-- 段が 1 以上の principal な添字。 -/
def enumPrin1 : List B := (enumFree 3 4).filter fun s => match s with
  | .nd u .nil _ => u ≥ 1 | _ => false

#guard enumPrin1.length == 278
#guard enumPrin1.all fun s => (List.range 3).all fun d =>
  redP (auxA (matB s d)) == auxTarget (matB s d)
-- 前置きした対角の**深さ**は添字と等しくない (根が深さ 0 でないから)。
#guard !(enumPrin1.all fun s => (List.range 3).all fun d =>
  trMax (auxA (matB s d)) == gp1 (psM (matB s d)) 0 - 1)

end

/-! ## §36 WHAT `red` REALLY COMPUTES: DEPTH BECOMES TREE DEPTH

§35 found that `red`'s own recursion leaves §31's class: the matrix `red_head_pos` builds has
a depth jump at the junction, so `StepOK` fails, and so does it for the matrices the fold then
hands to the recursive call.  A statement that is not closed under the recursion cannot be the
induction hypothesis, so this is the third and last restatement — and this one is closed.

    anc0 X i    the number of proper row-0 ancestors of column i — its TREE DEPTH
    nrmBlk X    every column moved to depth (root's level + its tree depth), levels kept
    nrmM X      that, block by block

**`red` re-depths.**  It throws the input's depths away and rebuilds them from the tree: the
spine becomes `0, 1, 2, …` because a spine node's tree depth IS its index, a branch root lands
at its parent's index plus one because that is ITS tree depth, and so on down.  The only thing
carried over from the input is the tree and the levels.  `shiftToLvl` and `canonM` were the
same statement seen from inside the class where depth already equalled tree depth plus a
constant — the guards below show `nrmM = canonM` there.

MEASURED on three populations:

    normal-form indices, 4 depths      red = nrmM,  and nrmM = canonM
    `auxMat` of them (StepOK BROKEN)   red = nrmM
    NON-normal-form indices, 243       red = nrmM at ZERO of them

The last is the control that says which hypothesis is doing the work: it is the LEVEL
condition, not the depth one.  `(0,0)(1,2)` has a level-2 node under a level-0 one; `red`
lowers it to `(0,0)(1,1)` while `nrmM`, which keeps levels, does not — so `red = nrmM` needs
`LvlOK` and needs nothing about `StepOK`. -/

section
open Trans.Recal
/-- 木の深さ = 行 0 の親鎖の長さ。 -/
def anc0 (X : Matrix) (i : Nat) : Nat := (iterParent (parent X 0) X.length i).length

/-- ブロックを「根の段 + 木の深さ」の位置へ置き直したもの。 -/
def nrmBlk (X : Matrix) : PS :=
  (List.range X.length).map fun i =>
    (((ent X 0 1 + anc0 X i : Nat) : Int), ((ent X i 1 : Nat) : Int))

/-- 行列をブロックごとに置き直したもの — **`red` の値**。 -/
def nrmM (X : Matrix) : PS := ((blocks X).map nrmBlk).flatten

/-- 対角の行列。 -/
def diagMat (k : Nat) : Matrix := (List.range k).map fun j => [j, j]

/-- `red_head_pos` が作る行列 (行列版)。 -/
def auxMat (X : Matrix) : Matrix := diagMat (ent X 0 1) ++ sh (ent X 0 1) X

/-- 段が 1 以上の principal な添字。 -/
def enumPrinPos : List B := (enumFree 3 4).filter fun s => match s with
  | .nd u .nil _ => u ≥ 1 | _ => false

/-- 標準形でない添字 (対照)。 -/
def enumBad : List B :=
  ((List.range 5).flatMap (enumNodes 3)).filter fun t => t != .nil && !(nfFree t)

-- 標準形の母集団では `red` の値であり、§31 の `canonM` と同じもの。
#guard (enumFree 3 4).all fun s => (List.range 3).all fun d =>
  redP (psM (matB s d)) == nrmM (matB s d)
#guard (enumFree 3 4).all fun s => (List.range 3).all fun d =>
  nrmM (matB s d) == canonM (matB s d)
-- **`StepOK` を壊す `auxMat` でも成り立つ。**
#guard enumPrinPos.length == 278
#guard enumPrinPos.all fun s => (List.range 3).all fun d =>
  redP (psM (auxMat (matB s d))) == nrmM (auxMat (matB s d))
#guard !(enumPrinPos.all fun s => (List.range 3).all fun d =>
  (List.range ((auxMat (matB s d)).length)).all fun j =>
    ent (auxMat (matB s d)) (j + 1) 0 ≤ ent (auxMat (matB s d)) j 0 + 1)
-- CTRL 標準形でない添字では **1 つも** 成り立たない。
#guard enumBad.length == 243
#guard (enumBad.filter fun s => redP (psM (matB s 0)) == nrmM (matB s 0)).length == 0
#guard redP (psM [[0, 0], [1, 2]]) == psM [[0, 0], [1, 1]]
#guard nrmM [[0, 0], [1, 2]] == psM [[0, 0], [1, 2]]

end

/-! ## §37 THE CLASS, AND A CHECK I SHOULD HAVE RUN THREE SECTIONS AGO

§20 stated the identity for `matB` indices, §31 restated it for `NFM` matrices, §36 restated
it again for `nrmM`.  Each restatement happened for the same reason: the recursion inside
`red` produced a matrix the previous class did not contain.  The check that would have caught
all three at once is "are `red`'s own recursive destinations in the class", and this section
runs it — on matrices generated freely, not from `B`.

The class is one condition, and it is about LEVELS only:

    LvlOKb X : every column's level is at most its row-0 parent's level plus one

MEASURED over all 9999 nonempty matrices of at most four columns with entries below 3:

    8844 satisfy LvlOKb, and red = nrmM at every one of them
    1155 do not,        and red = nrmM at NONE of them

so the condition is not merely sufficient — it is exactly the hypothesis.  And the three
destinations of `red`'s recursion stay inside it:

    the blocks of the `ppair` branch                     LvlOKb preserved
    `downMat` — the `red_shift` branch                   LvlOKb preserved
    `auxMat`  — the `red_head_pos` branch (942 cases)    LvlOKb preserved, red = nrmM there too

`auxMat` is the one that broke `NFM`, and it is fine here because `LvlOKb` never mentions
depths.  Note the guard is over the matrices `auxMat` is actually applied to — a single block
whose root has positive level; prepending a diagonal to something else is not what `red`
does, and does not preserve the condition. -/

section
open Trans.Recal
/-- **木の親に対する段の条件。** 深さの段差については何も言わない。 -/
def LvlOKb (X : Matrix) : Bool :=
  (List.range X.length).all fun i =>
    match parent X 0 i with
    | none => true
    | some p => decide (ent X i 1 ≤ ent X p 1 + 1)

/-- 高さ 2 の列を全部 (成分 < K)。 -/
def allCols (K : Nat) : List Col :=
  (List.range K).flatMap fun a => (List.range K).map fun b => [a, b]

/-- 長さ `n` 以下の行列を全部。 -/
def allMats (K : Nat) : Nat → List Matrix
  | 0 => [[]]
  | n + 1 => (allMats K n) ++ ((allMats K n).flatMap fun M => (allCols K).map fun c => M ++ [c])

def freePop : List Matrix := (allMats 3 4).filter fun M => !M.isEmpty
def freePopL : List Matrix := freePop.filter LvlOKb

/-- ブロック 1 つか (Bool 版)。 -/
def blkBool (X : Matrix) : Bool :=
  0 < X.length && (List.range X.length).all fun p => p == 0 || ent X 0 0 < ent X p 0

/-- 深さを根の分だけ下げたもの (`red_shift` の行き先)。 -/
def downMat (X : Matrix) : Matrix := X.map fun c => [c.getD 0 0 - ent X 0 0, c.getD 1 0]

#guard freePop.length == 9999
#guard freePopL.length == 8844
-- **両向きの一致。** `red = nrmM` はちょうど `LvlOKb` のところで成り立つ。
#guard freePopL.all fun M => redP (psM M) == nrmM M
#guard (freePop.filter fun M => !(LvlOKb M) && redP (psM M) == nrmM M).length == 0
-- **`red` の再帰の行き先はすべてこの類の中。**
#guard freePopL.all fun M => (blocks M).all LvlOKb
#guard freePopL.all fun M => LvlOKb (downMat M)
#guard (freePopL.filter fun M => blkBool M && 1 ≤ ent M 0 1).length == 942
#guard (freePopL.filter fun M => blkBool M && 1 ≤ ent M 0 1).all fun M => LvlOKb (auxMat M)
#guard (freePopL.filter fun M => blkBool M && 1 ≤ ent M 0 1).all fun M =>
  redP (psM (auxMat M)) == nrmM (auxMat M)

end

/-! ## §38 TREE DEPTH

`nrmM` is written in terms of `anc0` — the length of a column's row-0 parent chain, its TREE
DEPTH — so proving `red = nrmM` needs that quantity to behave.  Three facts, and the proofs
are the ones the name suggests.

`anc0` is well defined at all: the chain from `i` is decreasing, so any fuel of at least `i`
gives the same list (`iterParent_stable`), and `anc0` may therefore be unfolded one step
(`anc0_succ`: a column's tree depth is its parent's plus one) without worrying about which
fuel the definition happened to use.

    anc0_spine : on a run whose row-0 parent is always the previous column, tree depth = index

which is why `red`'s output starts `(0,0)(1,1)(2,2)…`: those columns' tree depths ARE their
indices, and `nrmM` puts every column at `root level + tree depth`.

    anc0_blk : inside a block sitting at position `s`, tree depth = the block root's plus the
               tree depth within the block

and that is what makes the recursion line up — the fold hands each branch to `red`, which
re-depths it from ITS own root, and `anc0_blk` says that agrees with re-depthing the whole
matrix at once.  Its ingredient is `parent_in_blk`: a column strictly inside a block finds its
parent inside the same block, because the block's own root is always a candidate and every
candidate outside sits further left. -/

section
open Trans.Recal

/-- 親鎖は燃料に依らない (親は真に減るので、`i` 以上あれば足りる)。 -/
theorem iterParent_stable (X : Matrix) : ∀ (f g i : Nat), i ≤ f → f ≤ g →
    iterParent (parent X 0) f i = iterParent (parent X 0) g i := by
  intro f
  induction f with
  | zero =>
    intro g i hi _
    have hi0 : i = 0 := by omega
    subst hi0
    cases g with
    | zero => rfl
    | succ h => rw [iterParent_nil (show parent X 0 0 = none from rfl)]; rfl
  | succ f' ih =>
    intro g i hi hfg
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    cases hp : parent X 0 i with
    | none => rw [iterParent_nil hp, iterParent_nil hp]
    | some p =>
      have hpi : p < i := by
        obtain ⟨hm, _⟩ := List.max?_eq_some_iff.mp hp
        exact List.mem_range.mp (List.mem_filter.mp hm).1
      rw [iterParent_cons hp, iterParent_cons hp, ih g' p (by omega) (by omega)]

theorem anc0_zero (X : Matrix) : anc0 X 0 = 0 := by
  show (iterParent (parent X 0) X.length 0).length = 0
  cases hn : X.length with
  | zero => rfl
  | succ g => rw [iterParent_nil (show parent X 0 0 = none from rfl)]; rfl

/-- 木の深さは親のそれに 1 を足したもの。 -/
theorem anc0_succ (X : Matrix) (i p : Nat) (hi : i < X.length)
    (h : parent X 0 i = some p) : anc0 X i = anc0 X p + 1 := by
  have hpi : p < i := by
    obtain ⟨hm, _⟩ := List.max?_eq_some_iff.mp h
    exact List.mem_range.mp (List.mem_filter.mp hm).1
  obtain ⟨g, hg⟩ : ∃ g, X.length = g + 1 := ⟨X.length - 1, by omega⟩
  show (iterParent (parent X 0) X.length i).length = (iterParent (parent X 0) X.length p).length + 1
  rw [hg, iterParent_cons h, List.length_cons,
    iterParent_stable X g (g + 1) p (by omega) (by omega)]

/-- 対角の上では木の深さは添字そのもの。 -/
theorem anc0_spine (X : Matrix) (tr : Nat) (htr : tr < X.length)
    (hpar : ∀ j, 1 ≤ j → j ≤ tr → parent X 0 j = some (j - 1)) :
    ∀ j, j ≤ tr → anc0 X j = j := by
  intro j
  induction j with
  | zero => intro _; exact anc0_zero X
  | succ k ih =>
    intro hk
    rw [anc0_succ X (k + 1) k (by omega) (by
      have := hpar (k + 1) (by omega) hk
      rw [show k + 1 - 1 = k from by omega] at this
      exact this), ih (by omega)]

/-! ### ブロックの中の親は中に留まる -/

/-- ブロックの内側の列は、そのブロックの中に親を持つ。 -/
theorem parent_blk_some (Bk : Matrix) (q : Nat) (hq : 0 < q) (hqlen : q < Bk.length)
    (hblk : BlkG Bk) : ∃ p, parent Bk 0 q = some p := by
  have hmem : 0 ∈ (List.range q).filter (fun c => decide (ent Bk c 0 < ent Bk q 0)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hq, decide_eq_true (hblk.2 q hq hqlen)⟩
  cases hp : parent Bk 0 q with
  | none =>
    exfalso
    rw [List.max?_eq_none_iff.mp hp] at hmem
    exact absurd hmem (by simp)
  | some p => exact ⟨p, rfl⟩

/-- ブロックが `s` の位置にあるとき、内側の列の親は `s` だけずれた同じもの。 -/
theorem parent_in_blk (M : Matrix) (s : Nat) (Bk : Matrix) (q p : Nat)
    (hpos : ∀ i, i < Bk.length → ent M (s + i) 0 = ent Bk i 0)
    (hqlen : q < Bk.length) (hp : parent Bk 0 q = some p) :
    parent M 0 (s + q) = some (s + p) := by
  obtain ⟨hpm, hpmax⟩ := List.max?_eq_some_iff.mp hp
  have hpq : p < q := List.mem_range.mp (List.mem_filter.mp hpm).1
  have hplt : ent Bk p 0 < ent Bk q 0 := of_decide_eq_true (List.mem_filter.mp hpm).2
  refine List.max?_eq_some_iff.mpr ⟨?_, ?_⟩
  · refine List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), decide_eq_true ?_⟩
    rw [hpos p (by omega), hpos q hqlen]
    exact hplt
  · intro c hc
    have hcr : c < s + q := List.mem_range.mp (List.mem_filter.mp hc).1
    have hclt : ent M c 0 < ent M (s + q) 0 := of_decide_eq_true (List.mem_filter.mp hc).2
    rcases Nat.lt_or_ge c s with hcs | hcs
    · omega
    · obtain ⟨p', rfl⟩ : ∃ p', c = s + p' := ⟨c - s, by omega⟩
      have hp'q : p' < q := by omega
      have : ent Bk p' 0 < ent Bk q 0 := by
        rw [← hpos p' (by omega), ← hpos q hqlen]
        exact hclt
      have := hpmax p' (List.mem_filter.mpr
        ⟨List.mem_range.mpr hp'q, decide_eq_true this⟩)
      omega

/-- **ブロックの中の木の深さは、ブロックの根の木の深さに足したもの。** -/
theorem anc0_blk (M : Matrix) (s : Nat) (Bk : Matrix)
    (hpos : ∀ i, i < Bk.length → ent M (s + i) 0 = ent Bk i 0)
    (hblk : BlkG Bk) (hlen : s + Bk.length ≤ M.length) :
    ∀ (n q : Nat), q ≤ n → q < Bk.length → anc0 M (s + q) = anc0 M s + anc0 Bk q := by
  intro n
  induction n with
  | zero =>
    intro q hq _
    rw [show q = 0 from by omega, show s + 0 = s from by omega, anc0_zero Bk]
    omega
  | succ g ih =>
    intro q hqn hq
    rcases Nat.eq_zero_or_pos q with rfl | hqpos
    · rw [show s + 0 = s from by omega, anc0_zero Bk]
      omega
    · obtain ⟨p, hp⟩ := parent_blk_some Bk q hqpos hq hblk
      have hpq : p < q := by
        obtain ⟨hm, _⟩ := List.max?_eq_some_iff.mp hp
        exact List.mem_range.mp (List.mem_filter.mp hm).1
      rw [anc0_succ M (s + q) (s + p) (by omega)
          (parent_in_blk M s Bk q p hpos hq hp),
        ih p (by omega) (by omega), anc0_succ Bk q p hq hp]
      omega

end

/-! ## §39 THE SPINE, WITHOUT ANY DEPTH HYPOTHESIS

§27 got the spine's shape out of `matB`'s two step bounds.  §37 says the class is `LvlOKb`
alone, so the spine has to come out of that — and it does, because the run's own condition
supplies what the depth bound used to.

The run says consecutive depths increase, and that alone makes column `j` the PARENT of column
`j + 1` (`parent_succ_of_lt`: it is a candidate, and no index between them exists).  With the
parent identified, `LvlOKb` caps the level at the previous one plus one while the run forces
it strictly higher — so it goes up by exactly one, and

    spine_lvl  : level = index along the run
    spine_anc0 : tree depth = index along the run   (§38's `anc0_spine`, same parent chain)

Note what is NOT assumed: nothing about depths beyond "they increase".  §27's `spine_diag_matB`
needed `matB_step_depth` to pin the depth to the index as well; here the depths may do
anything increasing, which is exactly the freedom `auxMat` needs.

`nrmBlk_take` reads the consequence off `nrmM`: since `nrmM` puts every column at
`root level + tree depth` and the run has root level 0 and tree depth = index, the first
`tr + 1` columns of the answer are `jjSeq 0 tr` — the diagonal `red` cuts. -/

section
open Trans.Recal

/-- 隣が浅ければそれが親 (最大の候補だから)。 -/
theorem parent_succ_of_lt (M : Matrix) (j : Nat) (h : ent M j 0 < ent M (j + 1) 0) :
    parent M 0 (j + 1) = some j := by
  refine List.max?_eq_some_iff.mpr ⟨?_, ?_⟩
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), decide_eq_true h⟩
  · intro b hb
    have := List.mem_range.mp (List.mem_filter.mp hb).1
    omega

/-- `LvlOKb` を 1 点で使う。 -/
theorem lvlOKb_at (M : Matrix) (h : LvlOKb M = true) (i p : Nat) (hi : i < M.length)
    (hp : parent M 0 i = some p) : ent M i 1 ≤ ent M p 1 + 1 := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [hp] at this
  exact of_decide_eq_true this

/-- **走りの上では段は添字そのもの。** 深さについては何も要らない。 -/
theorem spine_lvl (M : Matrix) (tr : Nat) (h0 : ent M 0 1 = 0)
    (hlvl : LvlOKb M = true) (hlen : tr < M.length)
    (hrun : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1) :
    ∀ j, j ≤ tr → ent M j 1 = j := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    have hpk := ih (by omega)
    have hr := hrun k (by omega)
    have hpar : parent M 0 (k + 1) = some k := parent_succ_of_lt M k hr.1
    have hle := lvlOKb_at M hlvl (k + 1) k (by omega) hpar
    omega

/-- 走りの上の親は 1 つ左。 -/
theorem spine_parent (M : Matrix) (tr : Nat)
    (hrun : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1) :
    ∀ j, 1 ≤ j → j ≤ tr → parent M 0 j = some (j - 1) := by
  intro j hj1 hjtr
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [show k + 1 - 1 = k from by omega]
  exact parent_succ_of_lt M k (hrun k (by omega)).1

/-- **走りの上では木の深さも添字そのもの。** -/
theorem spine_anc0 (M : Matrix) (tr : Nat) (hlen : tr < M.length)
    (hrun : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1) :
    ∀ j, j ≤ tr → anc0 M j = j :=
  anc0_spine M tr hlen (spine_parent M tr hrun)

/-- 走りの上での `nrmM` の列 — 対角そのもの。 -/
theorem nrmBlk_spine (M : Matrix) (tr : Nat) (h0 : ent M 0 1 = 0)
    (hlvl : LvlOKb M = true) (hlen : tr < M.length)
    (hrun : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1) :
    ∀ j, j ≤ tr → (nrmBlk M).getD j (0, 0) = (((j : Nat) : Int), ((j : Nat) : Int)) := by
  intro j hj
  show ((List.range M.length).map (fun i =>
    (((ent M 0 1 + anc0 M i : Nat) : Int), ((ent M i 1 : Nat) : Int)))).getD j (0, 0) = _
  rw [getD_map_range M.length _ (0, 0) j (by omega), h0,
    spine_anc0 M tr hlen hrun j hj, spine_lvl M tr h0 hlvl hlen hrun j hj,
    show 0 + j = j from by omega]

theorem nrmBlk_length (M : Matrix) : (nrmBlk M).length = M.length := by
  show ((List.range M.length).map _).length = _
  rw [List.length_map, List.length_range]

/-- **`nrmM` の頭は対角そのもの。** -/
theorem nrmBlk_take (M : Matrix) (tr : Nat) (h0 : ent M 0 1 = 0)
    (hlvl : LvlOKb M = true) (hlen : tr < M.length)
    (hrun : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1) :
    (nrmBlk M).take (tr + 1) = jjSeq 0 ((tr : Nat) : Int) := by
  rw [take_eq_map_range ((0 : Int), (0 : Int)) (tr + 1) (nrmBlk M)
      (by rw [nrmBlk_length]; omega),
    jjSeq_zero tr]
  exact List.map_congr_left (fun i hi => nrmBlk_spine M tr h0 hlvl hlen hrun i
    (by have := List.mem_range.mp hi; omega))

end

/-! ## §40 THE THREE BRANCHES THAT DO NOT RECURSE INTO THEMSELVES

§34 started the induction against `canonM`; §36–§37 replaced the target by `nrmM` and the
class by `LvlOKb`, so the skeleton has to be restated once — it is the same three lines
(`redN_nil`, `redN_sum`, `nrmM_single`), now against `nrmBlk`.

Then the two branches of the one-block case that end immediately:

    redN_leaf  : one column.  §21's `red_leaf` already puts it at (v, v), and that IS `nrmBlk`
                 of a one-column matrix — tree depth 0, so depth = root level = v.
    redN_shift : root at level 0 and depth d > 0.  `red` subtracts d from every depth and
                 recurses; the matrix it recurses into is `downMat X`.

`downMat` is invisible to the answer, and this section says so four times over: lowering every
depth by the same amount leaves the row-0 PARENT unchanged (`parent_downMat` — the comparison
`ent X p 0 < ent X i 0` is what the parent is defined by, and subtracting a constant from both
sides of a comparison between numbers that are both at least that constant does nothing), hence
leaves tree depth unchanged (`anc0_downMat`, via `iterParent_congr`), hence leaves `nrmBlk`
unchanged (`nrmBlk_downMat`) and `LvlOKb` unchanged (`lvlOKb_downMat`) — the last is what makes
the branch legal as an induction step at all, since the class must contain the destination.

The block hypothesis `BlkG X` is what makes the subtraction safe: the root is the shallowest
column, so `ent X i 0 - ent X 0 0` never truncates. -/

section
open Trans.Recal


/-! ### `nrmM` の側の言い直し -/

theorem nrmM_nil : nrmM ([] : Matrix) = [] := by
  show ((blocks ([] : Matrix)).map nrmBlk).flatten = _
  rw [blocks_nil]
  rfl

theorem nrmM_single (X : Matrix) (h : BlkG X) : nrmM X = nrmBlk X := by
  show ((blocks X).map nrmBlk).flatten = _
  rw [blocks_single X h]
  show nrmBlk X ++ [] = _
  rw [List.append_nil]

theorem redN_nil (f : Nat) : red f (psM ([] : Matrix)) = nrmM [] := by
  rw [nrmM_nil]
  show red f ([] : PS) = _
  cases f with
  | zero => rfl
  | succ g =>
    rw [red_nonprin [] g (by decide) (by decide), show ppair ([] : PS) = [] from by decide]
    rfl

/-- 最上位のブロックが 2 つ以上の場合 (`nrmM` 版)。 -/
theorem redN_sum (f : Nat) (X : Matrix) (hzero : isZeroP (psM X) = false)
    (hprin : isPrincipalP (psM X) = false)
    (ih : ∀ Bk ∈ blocks X, red f (psM Bk) = nrmBlk Bk) :
    red (f + 1) (psM X) = nrmM X := by
  rw [red_nonprin _ f hzero hprin, ppair_blocksG, List.flatMap_map]
  show ((blocks X).map (fun Bk => red f (psM Bk))).flatten = _
  rw [List.map_congr_left ih]
  rfl

/-! ### 深さを根の分だけ下げる -/

theorem downMat_length (X : Matrix) : (downMat X).length = X.length := List.length_map ..

theorem ent_downMat0 (X : Matrix) (i : Nat) (hi : i < X.length) :
    ent (downMat X) i 0 = ent X i 0 - ent X 0 0 := by
  show ((X.map (fun c => [c.getD 0 0 - ent X 0 0, c.getD 1 0])).getD i []).getD 0 0 = _
  rw [getD_map_lt _ X [] [] i hi]
  rfl

theorem ent_downMat1 (X : Matrix) (i : Nat) (hi : i < X.length) :
    ent (downMat X) i 1 = ent X i 1 := by
  show ((X.map (fun c => [c.getD 0 0 - ent X 0 0, c.getD 1 0])).getD i []).getD 1 0 = _
  rw [getD_map_lt _ X [] [] i hi]
  rfl

theorem parent0_lt (M : Matrix) (i p : Nat) (h : parent M 0 i = some p) : p < i := by
  obtain ⟨hm, _⟩ := List.max?_eq_some_iff.mp h
  exact List.mem_range.mp (List.mem_filter.mp hm).1

theorem blkG_ge (X : Matrix) (h : BlkG X) (i : Nat) (hi : i < X.length) :
    ent X 0 0 ≤ ent X i 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · omega
  · exact Nat.le_of_lt (h.2 i hpos hi)

theorem blkG_downMat (X : Matrix) (h : BlkG X) : BlkG (downMat X) := by
  refine ⟨by rw [downMat_length]; exact h.1, ?_⟩
  intro p hp hplen
  rw [downMat_length] at hplen
  rw [ent_downMat0 X 0 h.1, ent_downMat0 X p hplen]
  have := h.2 p hp hplen
  omega

/-- 親は深さを一斉に下げても変わらない。 -/
theorem parent_downMat (X : Matrix) (h : BlkG X) (i : Nat) (hi : i < X.length) :
    parent (downMat X) 0 i = parent X 0 i := by
  show ((List.range i).filter (fun p => decide (ent (downMat X) p 0 < ent (downMat X) i 0))).max?
    = ((List.range i).filter (fun p => decide (ent X p 0 < ent X i 0))).max?
  refine congrArg List.max? (List.filter_congr (fun p hp => ?_))
  have hpi : p < i := List.mem_range.mp hp
  rw [ent_downMat0 X p (by omega), ent_downMat0 X i hi]
  have h1 := blkG_ge X h p (by omega)
  have h2 := blkG_ge X h i hi
  by_cases hc : ent X p 0 < ent X i 0
  · rw [decide_eq_true (show ent X p 0 - ent X 0 0 < ent X i 0 - ent X 0 0 from by omega),
      decide_eq_true hc]
  · rw [decide_eq_false (show ¬(ent X p 0 - ent X 0 0 < ent X i 0 - ent X 0 0) from by omega),
      decide_eq_false hc]

theorem iterParent_congr (F G : Nat → Option Nat) (n : Nat)
    (hlt : ∀ i p, F i = some p → p < i) (hfg : ∀ i, i < n → F i = G i) :
    ∀ (f i : Nat), i < n → iterParent F f i = iterParent G f i := by
  intro f
  induction f with
  | zero => intro _ _; rfl
  | succ g ih =>
    intro i hi
    cases hp : F i with
    | none =>
      rw [iterParent_nil hp, iterParent_nil (by rw [← hfg i hi]; exact hp)]
    | some p =>
      have hpi := hlt i p hp
      rw [iterParent_cons hp, iterParent_cons (show G i = some p from by rw [← hfg i hi]; exact hp),
        ih p (by omega)]

theorem anc0_downMat (X : Matrix) (h : BlkG X) (i : Nat) (hi : i < X.length) :
    anc0 (downMat X) i = anc0 X i := by
  show (iterParent (parent (downMat X) 0) (downMat X).length i).length
    = (iterParent (parent X 0) X.length i).length
  rw [downMat_length,
    iterParent_congr (parent (downMat X) 0) (parent X 0) X.length
      (fun a b hab => parent0_lt (downMat X) a b hab)
      (fun j hj => parent_downMat X h j hj) X.length i hi]

theorem nrmBlk_downMat (X : Matrix) (h : BlkG X) : nrmBlk (downMat X) = nrmBlk X := by
  show (List.range (downMat X).length).map _ = (List.range X.length).map _
  rw [downMat_length]
  refine List.map_congr_left (fun i hi => ?_)
  have hi' : i < X.length := List.mem_range.mp hi
  rw [ent_downMat1 X 0 h.1, ent_downMat1 X i hi', anc0_downMat X h i hi']

theorem lvlOKb_downMat (X : Matrix) (h : BlkG X) (hl : LvlOKb X = true) :
    LvlOKb (downMat X) = true := by
  show ((List.range (downMat X).length).all _) = true
  refine List.all_eq_true.mpr (fun i hi => ?_)
  have hi' : i < X.length := by
    have := List.mem_range.mp hi
    rw [downMat_length] at this
    exact this
  rw [parent_downMat X h i hi']
  cases hp : parent X 0 i with
  | none => rfl
  | some p =>
    have hpi := parent0_lt X i p hp
    have hall := lvlOKb_at X hl i p hi' hp
    show decide (ent (downMat X) i 1 ≤ ent (downMat X) p 1 + 1) = true
    rw [ent_downMat1 X i hi', ent_downMat1 X p (by omega)]
    exact decide_eq_true hall

theorem blkG_mem_ge (X : Matrix) (h : BlkG X) : ∀ c ∈ X, ent X 0 0 ≤ c.getD 0 0 := by
  intro c hc
  obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hc
  have hxi : X.getD i [] = c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hci]
    rfl
  have heq : ent X i 0 = c.getD 0 0 := by
    rw [show ent X i 0 = (X.getD i []).getD 0 0 from rfl, hxi]
  rw [← heq]
  exact blkG_ge X h i hi

theorem psM_downMat (X : Matrix) (h : BlkG X) :
    incrFirst (psM X) (-((ent X 0 0 : Nat) : Int)) = psM (downMat X) := by
  show ((X.map (fun c => (((c.getD 0 0 : Nat) : Int), ((c.getD 1 0 : Nat) : Int)))).map
      (fun c => (c.1 + -((ent X 0 0 : Nat) : Int), c.2)))
    = (X.map (fun c => [c.getD 0 0 - ent X 0 0, c.getD 1 0])).map
      (fun c => (((c.getD 0 0 : Nat) : Int), ((c.getD 1 0 : Nat) : Int)))
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun c hc => ?_)
  have hge := blkG_mem_ge X h c hc
  show ((((c.getD 0 0 : Nat) : Int) + -((ent X 0 0 : Nat) : Int)), ((c.getD 1 0 : Nat) : Int))
    = ((((c.getD 0 0 - ent X 0 0 : Nat)) : Int), ((c.getD 1 0 : Nat) : Int))
  rw [show (((c.getD 0 0 - ent X 0 0 : Nat)) : Int)
      = ((c.getD 0 0 : Nat) : Int) + -((ent X 0 0 : Nat) : Int) from by omega]

/-- ブロック 1 つ・根の段 0・根の深さ > 0 — 深さを根の分だけ下げるだけ。 -/
theorem redN_shift (f : Nat) (X : Matrix) (h : BlkG X) (hlen : 1 < X.length)
    (hlvl0 : ent X 0 1 = 0) (hdep : 0 < ent X 0 0) :
    red (f + 1) (psM X) = red f (psM (downMat X)) := by
  have hg0 : gp0 (psM X) 0 = ((ent X 0 0 : Nat) : Int) := psM_gp0 X 0
  have hg1a : gp1 (psM X) 0 = ((ent X 0 1 : Nat) : Int) := psM_gp1 X 0
  have hg1 : gp1 (psM X) 0 = 0 := by rw [hg1a, hlvl0]; rfl
  rw [Rows.Ladder.red_shift _ f
      (by
        show ((psM X).length == 1 && _) = false
        rw [show ((psM X).length == 1) = false from by
          rw [psM_len]; exact decide_eq_false (by omega)]
        rfl)
      (prin_of_deep X hlen h.2)
      (by rw [hg0]; exact decide_eq_false (by omega)) hg1,
    hg0, psM_downMat X h]

/-- 1 列のブロック — `red_leaf` がそのまま `nrmBlk` を返す。 -/
theorem redN_leaf (d v f : Nat) : red (f + 2) (psM [[d, v]]) = nrmBlk [[d, v]] := by
  show red (f + 2) [(((d : Nat) : Int), ((v : Nat) : Int))] = _
  rw [red_leaf d f v]
  rfl

end

/-! ## §41 THE COLUMN `red` BUILDS FOR A BRANCH

The fold hands each branch to `red` after replacing the branch's ROOT column by one built from
indices: `(row-0 parent index + 1, row-1 parent index + 1)`.  §32 read those two numbers off in
the region's setting, where the spine's depth equals its index and the two readings coincide.
In the `LvlOKb` setting they need not, so this section separates them.

The level is fine: §39 gives level = index along the run without any depth hypothesis, so the
row-1 parent index plus one IS the branch root's level (that is §35's `fpar_one_spine'`).

The depth is NOT the branch root's depth — it is `p + 1`, an index plus one.  What saves the
proof is that the answer never looks at a block root's depth:

    setRoot e X          the matrix with the root's depth replaced by `e`
    parent_setRoot       the row-0 parent is unchanged, as long as `e` still undercuts the rest
    anc0_setRoot         hence so is the tree depth
    nrmBlk_setRoot       hence so is `nrmM`'s answer for the block
    lvlOKb_setRoot       and the class is preserved, so the branch is a legal induction step

`parent_congr` / `anc0_congr` are the general form: the tree is a function of the depth
COMPARISONS alone, so any change that preserves every comparison preserves the tree.  (§40's
`downMat` is the other instance of the same principle.)

The side condition — `e` undercuts every other column of the branch — comes from
`spine_depth_ge`: a run that starts at depth 0 and strictly increases has `depth ≥ index`, so
the parent `p` on the spine has `ent X p 0 ≥ p`, the branch root is deeper than that, and every
other column of the branch is deeper still.  Hence `p + 1 ≤ branch root's depth < the rest`. -/

section
open Trans.Recal


/-! ### 木は深さの大小しか見ない -/

theorem parent_congr (X Y : Matrix)
    (h : ∀ p i, p < i → i < X.length →
      decide (ent X p 0 < ent X i 0) = decide (ent Y p 0 < ent Y i 0)) :
    ∀ i, i < X.length → parent X 0 i = parent Y 0 i := by
  intro i hi
  show ((List.range i).filter (fun p => decide (ent X p 0 < ent X i 0))).max?
    = ((List.range i).filter (fun p => decide (ent Y p 0 < ent Y i 0))).max?
  exact congrArg List.max? (List.filter_congr (fun p hp => h p i (List.mem_range.mp hp) hi))

theorem anc0_congr (X Y : Matrix) (hlen : X.length = Y.length)
    (h : ∀ i, i < X.length → parent X 0 i = parent Y 0 i) :
    ∀ i, i < X.length → anc0 X i = anc0 Y i := by
  intro i hi
  show (iterParent (parent X 0) X.length i).length
    = (iterParent (parent Y 0) Y.length i).length
  rw [← hlen,
    iterParent_congr (parent X 0) (parent Y 0) X.length
      (fun a b hab => parent0_lt X a b hab) h X.length i hi]

/-! ### 根の深さだけを取り替える -/

/-- 根の深さを `e` に取り替えたもの — `red` が枝の先頭に作る列。 -/
def setRoot (e : Nat) : Matrix → Matrix
  | [] => []
  | c :: cs => (e :: c.drop 1) :: cs

theorem setRoot_length (e : Nat) : ∀ (X : Matrix), (setRoot e X).length = X.length
  | [] => rfl
  | _ :: _ => rfl

theorem ent_setRoot_root (e : Nat) (c : Col) (cs : Matrix) :
    ent (setRoot e (c :: cs)) 0 0 = e := rfl

theorem ent_setRoot_pos (e : Nat) (c : Col) (cs : Matrix) (i : Nat) :
    ent (setRoot e (c :: cs)) (i + 1) 0 = ent (c :: cs) (i + 1) 0 := rfl

theorem ent_setRoot_lvl (e : Nat) : ∀ (X : Matrix) (i : Nat),
    ent (setRoot e X) i 1 = ent X i 1
  | [], _ => rfl
  | c :: _, 0 => by
    show (e :: c.drop 1).getD 1 0 = c.getD 1 0
    exact getD_drop_one c
  | _ :: _, _ + 1 => rfl

/-- 取り替えても根が一番浅いままなら、親はどれも変わらない。 -/
theorem parent_setRoot (e : Nat) (X : Matrix) (hblk : BlkG X)
    (hlo : ∀ p, 0 < p → p < X.length → e < ent X p 0) :
    ∀ i, i < X.length → parent (setRoot e X) 0 i = parent X 0 i := by
  intro i0 hi0
  refine parent_congr (setRoot e X) X (fun p i hpi hi => ?_) i0
    (by rw [setRoot_length]; exact hi0)
  rw [setRoot_length] at hi
  cases X with
  | nil => exact absurd hi (by simp)
  | cons c cs =>
    cases p with
    | zero =>
      obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
      rw [ent_setRoot_root e c cs, ent_setRoot_pos e c cs q]
      rw [decide_eq_true (hlo (q + 1) (by omega) hi),
        decide_eq_true (hblk.2 (q + 1) (by omega) hi)]
    | succ r =>
      obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
      rw [ent_setRoot_pos e c cs r, ent_setRoot_pos e c cs q]

theorem blkG_setRoot (e : Nat) (X : Matrix) (hblk : BlkG X)
    (hlo : ∀ p, 0 < p → p < X.length → e < ent X p 0) : BlkG (setRoot e X) := by
  refine ⟨by rw [setRoot_length]; exact hblk.1, ?_⟩
  intro p hp hplen
  rw [setRoot_length] at hplen
  cases X with
  | nil => exact absurd hplen (by simp)
  | cons c cs =>
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [ent_setRoot_root e c cs, ent_setRoot_pos e c cs q]
    exact hlo (q + 1) (by omega) hplen

theorem anc0_setRoot (e : Nat) (X : Matrix) (hblk : BlkG X)
    (hlo : ∀ p, 0 < p → p < X.length → e < ent X p 0) :
    ∀ i, i < X.length → anc0 (setRoot e X) i = anc0 X i := by
  intro i hi
  exact anc0_congr (setRoot e X) X (setRoot_length e X)
    (fun j hj => parent_setRoot e X hblk hlo j (by rw [setRoot_length] at hj; exact hj))
    i (by rw [setRoot_length]; exact hi)

/-- **答えは根の深さを見ていない。** -/
theorem nrmBlk_setRoot (e : Nat) (X : Matrix) (hblk : BlkG X)
    (hlo : ∀ p, 0 < p → p < X.length → e < ent X p 0) :
    nrmBlk (setRoot e X) = nrmBlk X := by
  show (List.range (setRoot e X).length).map _ = (List.range X.length).map _
  rw [setRoot_length]
  refine List.map_congr_left (fun i hi => ?_)
  have hi' : i < X.length := List.mem_range.mp hi
  rw [ent_setRoot_lvl e X 0, ent_setRoot_lvl e X i, anc0_setRoot e X hblk hlo i hi']

theorem lvlOKb_setRoot (e : Nat) (X : Matrix) (hblk : BlkG X)
    (hlo : ∀ p, 0 < p → p < X.length → e < ent X p 0) (hl : LvlOKb X = true) :
    LvlOKb (setRoot e X) = true := by
  show ((List.range (setRoot e X).length).all _) = true
  refine List.all_eq_true.mpr (fun i hi => ?_)
  have hi' : i < X.length := by
    have := List.mem_range.mp hi
    rw [setRoot_length] at this
    exact this
  rw [parent_setRoot e X hblk hlo i hi']
  cases hp : parent X 0 i with
  | none => rfl
  | some p =>
    have hpi := parent0_lt X i p hp
    have hall := lvlOKb_at X hl i p hi' hp
    show decide (ent (setRoot e X) i 1 ≤ ent (setRoot e X) p 1 + 1) = true
    rw [ent_setRoot_lvl e X i, ent_setRoot_lvl e X p]
    exact decide_eq_true hall

/-- 取り替えた行列の `psM` — `red` が枝へ渡す形そのもの。 -/
theorem psM_setRoot (e : Nat) (c : Col) (cs : Matrix) :
    psM (setRoot e (c :: cs))
      = (((e : Nat) : Int), ((ent (c :: cs) 0 1 : Nat) : Int)) :: derp (psM (c :: cs)) := by
  show (((e :: c.drop 1) :: cs).map _) = _
  show ((((e :: c.drop 1).getD 0 0 : Nat) : Int), (((e :: c.drop 1).getD 1 0 : Nat) : Int))
      :: cs.map (fun q => (((q.getD 0 0 : Nat) : Int), ((q.getD 1 0 : Nat) : Int))) = _
  rw [show ((e :: c.drop 1).getD 1 0) = ent (c :: cs) 0 1 from getD_drop_one c]
  rfl

/-! ### 対角の深さは添字以上 -/

theorem spine_depth_ge (M : Matrix) (tr : Nat) (h0 : ent M 0 0 = 0)
    (hrun : ∀ j, j < tr → ent M j 0 < ent M (j + 1) 0) :
    ∀ j, j ≤ tr → j ≤ ent M j 0 := by
  intro j
  induction j with
  | zero => intro _; omega
  | succ k ih =>
    intro hk
    have := hrun k (by omega)
    have := ih (by omega)
    omega

end

/-! ## §42 THE ANSWER SPLITS ALONG THE BRANCHES

The fold produces `jjSeq 0 tr ++ (one piece per branch).flatten`, so the answer has to be shown
to have that shape — and this section shows it without mentioning `red` at all.  It is about
`nrmM` and about lists.

`nrmBlk X` is a map over `List.range X.length`: every column's answer depends only on its
POSITION.  A list of blocks whose `flatten` is that range therefore cuts the map into pieces,
one per block, and that is `map_range_flatten` — proved by induction on the block list with the
running offset as the accumulator (`pieceList`).  `range_add_map` is the one-step case.

    nrmBlk_split       nrmBlk X = (first tr+1 positions) ++ (pieces of the blocks after them)
    nrmBlk_diag_split  and the first part is `jjSeq 0 tr` (§39)

Then the piece for one branch is identified: `pieceList_nrm` says it is `nrmBlk` OF THAT BRANCH,
translated.  The translation is `anc0 X s - (branch root's level)`, and the reason is §38's
`anc0_blk` — tree depth inside a block is the block root's tree depth plus the tree depth within
the block — so the position-indexed answer for column `s + i` and the block-indexed answer for
column `i` differ by a constant.  That constant is exactly what the algorithm's `incrFirst`
applies.

`getD_flatten_block` / `ent_brBlk` are the bookkeeping that says where the `J`-th block starts:
after the diagonal and after the blocks before it. -/

section
open Trans.Recal


/-! ### 範囲の写像を切り分ける -/

theorem range_add_map {β : Type _} (h : Nat → β) : ∀ (m n : Nat),
    (List.range (m + n)).map h
      = (List.range m).map h ++ (List.range n).map (fun i => h (m + i)) := by
  intro m n
  induction n with
  | zero =>
    show (List.range (m + 0)).map h = (List.range m).map h ++ []
    rw [List.append_nil, show m + 0 = m from by omega]
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 from by omega, List.range_succ, List.map_append,
      ih, List.append_assoc, List.range_succ, List.map_append]
    rfl

/-- ブロックごとの切り身。`base` はそのブロックの先頭が全体で占める位置。 -/
def pieceList {β γ : Type _} (G : Nat → β) : Nat → List (List γ) → List (List β)
  | _, [] => []
  | base, Bk :: rest =>
      ((List.range Bk.length).map (fun i => G (base + i)))
        :: pieceList G (base + Bk.length) rest

theorem pieceList_length {β γ : Type _} (G : Nat → β) :
    ∀ (base : Nat) (Bs : List (List γ)), (pieceList G base Bs).length = Bs.length
  | _, [] => rfl
  | base, Bk :: rest => by
      show (pieceList G (base + Bk.length) rest).length + 1 = rest.length + 1
      rw [pieceList_length G (base + Bk.length) rest]

/-- **位置で書いた列は、ブロックごとの切り身を並べたもの。** -/
theorem map_range_flatten {β γ : Type _} (G : Nat → β) :
    ∀ (Bs : List (List γ)) (base : Nat),
      (List.range (Bs.flatten.length)).map (fun i => G (base + i))
        = (pieceList G base Bs).flatten
  | [], _ => rfl
  | Bk :: rest, base => by
      show (List.range ((Bk ++ rest.flatten).length)).map (fun i => G (base + i))
        = ((List.range Bk.length).map (fun i => G (base + i)))
            ++ (pieceList G (base + Bk.length) rest).flatten
      rw [← map_range_flatten G rest (base + Bk.length), List.length_append,
        range_add_map (fun i => G (base + i)) Bk.length rest.flatten.length]
      refine congrArg (fun l => ((List.range Bk.length).map (fun i => G (base + i))) ++ l) ?_
      exact List.map_congr_left (fun i _ => by rw [show base + (Bk.length + i)
        = base + Bk.length + i from by omega])

theorem pieceList_getD {β γ : Type _} (G : Nat → β) :
    ∀ (Bs : List (List γ)) (base J : Nat), J < Bs.length →
      (pieceList G base Bs).getD J []
        = (List.range ((Bs.getD J []).length)).map
            (fun i => G (base + ((Bs.take J).flatten).length + i))
  | [], _, _, h => absurd h (by simp)
  | Bk :: rest, base, 0, _ => by
      show (List.range Bk.length).map (fun i => G (base + i)) = _
      show _ = (List.range Bk.length).map (fun i => G (base + ([] : List γ).length + i))
      refine List.map_congr_left (fun i _ => ?_)
      show G (base + i) = G (base + 0 + i)
      exact congrArg G (by omega)
  | Bk :: rest, base, K + 1, h => by
      have hK : K < rest.length := by
        have : (Bk :: rest).length = rest.length + 1 := rfl
        omega
      show (pieceList G (base + Bk.length) rest).getD K [] = _
      rw [pieceList_getD G rest (base + Bk.length) K hK]
      show (List.range ((rest.getD K []).length)).map
          (fun i => G (base + Bk.length + ((rest.take K).flatten).length + i))
        = (List.range ((rest.getD K []).length)).map
          (fun i => G (base + ((Bk ++ (rest.take K).flatten).length) + i))
      refine List.map_congr_left (fun i _ => ?_)
      rw [List.length_append, show base + Bk.length + ((rest.take K).flatten).length + i
        = base + (Bk.length + ((rest.take K).flatten).length) + i from by omega]

/-! ### `nrmBlk` を対角と枝に切る -/

/-- `nrmBlk` の `i` 番目 — 位置だけの関数。 -/
def nrmG (X : Matrix) (i : Nat) : Int × Int :=
  (((ent X 0 1 + anc0 X i : Nat) : Int), ((ent X i 1 : Nat) : Int))

theorem nrmBlk_eq_map (X : Matrix) : nrmBlk X = (List.range X.length).map (nrmG X) := rfl

/-- **答えは「対角の分」と「ブロックごとの切り身」に分かれる。** -/
theorem nrmBlk_split (X : Matrix) (tr : Nat) (htr : tr < X.length) :
    nrmBlk X = (List.range (tr + 1)).map (nrmG X)
      ++ (pieceList (nrmG X) (tr + 1) (blocks (X.drop (tr + 1)))).flatten := by
  rw [nrmBlk_eq_map X,
    show X.length = (tr + 1) + ((blocks (X.drop (tr + 1))).flatten).length from by
      rw [blocks_flatten (X.drop (tr + 1)).length (X.drop (tr + 1)) (Nat.le_refl _),
        List.length_drop]
      omega,
    range_add_map (nrmG X) (tr + 1) _,
    map_range_flatten (nrmG X) (blocks (X.drop (tr + 1))) (tr + 1)]

theorem nrmBlk_diag_split (X : Matrix) (tr : Nat) (h0 : ent X 0 1 = 0)
    (hlvl : LvlOKb X = true) (htr : tr < X.length)
    (hrun : ∀ j, j < tr → ent X j 0 < ent X (j + 1) 0 ∧ ent X j 1 < ent X (j + 1) 1) :
    nrmBlk X = jjSeq 0 ((tr : Nat) : Int)
      ++ (pieceList (nrmG X) (tr + 1) (blocks (X.drop (tr + 1)))).flatten := by
  rw [nrmBlk_split X tr htr,
    show (List.range (tr + 1)).map (nrmG X) = (nrmBlk X).take (tr + 1) from by
      rw [take_eq_map_range ((0 : Int), (0 : Int)) (tr + 1) (nrmBlk X)
        (by rw [nrmBlk_length]; omega)]
      exact List.map_congr_left (fun i hi =>
        (getD_map_range X.length (nrmG X) ((0 : Int), (0 : Int)) i
          (by have := List.mem_range.mp hi; omega)).symm),
    nrmBlk_take X tr h0 hlvl htr hrun]

/-! ### ブロックの居場所 -/

theorem getD_flatten_block {γ : Type _} (d : γ) :
    ∀ (Bs : List (List γ)) (J : Nat), J < Bs.length →
      ∀ (i : Nat), i < (Bs.getD J []).length →
        Bs.flatten.getD ((((Bs.take J).flatten).length) + i) d = (Bs.getD J []).getD i d
  | [], _, h, _, _ => absurd h (by simp)
  | Bk :: rest, 0, _, i, hi => by
      show (Bk ++ rest.flatten).getD (0 + i) d = Bk.getD i d
      rw [show 0 + i = i from by omega]
      exact getD_app_left Bk rest.flatten d i hi
  | Bk :: rest, K + 1, h, i, hi => by
      have hK : K < rest.length := by
        have hc : (Bk :: rest).length = rest.length + 1 := rfl
        omega
      show (Bk ++ rest.flatten).getD ((Bk ++ (rest.take K).flatten).length + i) d
        = (rest.getD K []).getD i d
      rw [List.length_append,
        getD_app_right Bk rest.flatten d _ (by omega),
        show Bk.length + ((rest.take K).flatten).length + i - Bk.length
          = ((rest.take K).flatten).length + i from by omega]
      exact getD_flatten_block d rest K hK i hi

theorem ent_flatten_block (Bs : List Matrix) (J : Nat) (hJ : J < Bs.length) (i y : Nat)
    (hi : i < (Bs.getD J []).length) :
    ent Bs.flatten ((((Bs.take J).flatten).length) + i) y = ent (Bs.getD J []) i y := by
  show (Bs.flatten.getD _ []).getD y 0 = ((Bs.getD J []).getD i []).getD y 0
  rw [getD_flatten_block ([] : Col) Bs J hJ i hi]

/-- 対角のあとの `J` 番目のブロックは `tr + 1 + 前の分` から始まる。 -/
theorem ent_brBlk (X : Matrix) (tr J : Nat)
    (hJ : J < (blocks (X.drop (tr + 1))).length) (i y : Nat)
    (hi : i < ((blocks (X.drop (tr + 1))).getD J []).length) :
    ent X (tr + 1 + ((((blocks (X.drop (tr + 1))).take J).flatten).length) + i) y
      = ent ((blocks (X.drop (tr + 1))).getD J []) i y := by
  have hfl : (blocks (X.drop (tr + 1))).flatten = X.drop (tr + 1) :=
    blocks_flatten (X.drop (tr + 1)).length (X.drop (tr + 1)) (Nat.le_refl _)
  have hb := ent_flatten_block (blocks (X.drop (tr + 1))) J hJ i y hi
  rw [hfl, ent_drop] at hb
  rw [show tr + 1 + ((((blocks (X.drop (tr + 1))).take J).flatten).length) + i
    = tr + 1 + (((((blocks (X.drop (tr + 1))).take J).flatten).length) + i) from by omega]
  exact hb

/-- **切り身はそのブロックの答えを平行移動したもの。** -/
theorem pieceList_nrm (X Bk : Matrix) (s : Nat) (Bs : List Matrix) (base J : Nat)
    (h0 : ent X 0 1 = 0) (hJ : J < Bs.length) (hBk : Bs.getD J [] = Bk)
    (hs : s = base + ((Bs.take J).flatten).length)
    (hpos : ∀ i, i < Bk.length → ent X (s + i) 0 = ent Bk i 0)
    (hlv : ∀ i, i < Bk.length → ent X (s + i) 1 = ent Bk i 1)
    (hblk : BlkG Bk) (hlen : s + Bk.length ≤ X.length) :
    (pieceList (nrmG X) base Bs).getD J []
      = incrFirst (nrmBlk Bk) (((anc0 X s : Nat) : Int) - ((ent Bk 0 1 : Nat) : Int)) := by
  rw [pieceList_getD (nrmG X) Bs base J hJ, hBk, ← hs]
  show (List.range Bk.length).map (fun i => nrmG X (s + i))
    = ((List.range Bk.length).map
        (fun i => (((ent Bk 0 1 + anc0 Bk i : Nat) : Int), ((ent Bk i 1 : Nat) : Int)))).map
      (fun q => (q.1 + (((anc0 X s : Nat) : Int) - ((ent Bk 0 1 : Nat) : Int)), q.2))
  rw [List.map_map]
  refine List.map_congr_left (fun i hi => ?_)
  have hi' : i < Bk.length := List.mem_range.mp hi
  show (((ent X 0 1 + anc0 X (s + i) : Nat) : Int), ((ent X (s + i) 1 : Nat) : Int))
    = ((((ent Bk 0 1 + anc0 Bk i : Nat) : Int)
        + (((anc0 X s : Nat) : Int) - ((ent Bk 0 1 : Nat) : Int))), ((ent Bk i 1 : Nat) : Int))
  rw [h0, anc0_blk X s Bk hpos hblk hlen i i (Nat.le_refl i) hi', hlv i hi',
    show ((0 + (anc0 X s + anc0 Bk i) : Nat) : Int)
      = (((ent Bk 0 1 + anc0 Bk i : Nat) : Int)
          + (((anc0 X s : Nat) : Int) - ((ent Bk 0 1 : Nat) : Int))) from by omega]

end

/-! ## §43 WHAT THE FOLD HANDS TO THE RECURSIVE CALL

The fold's `J`-th term is `incrFirst (red f NJ) (jnJ - nJ)` where

    NJ  = (jnJ + 1, nJ + 1) :: derp bJ        bJ = the J-th branch
    jnJ = joints.getD J                       the branch root's row-0 parent INDEX
    nJ  = -1 if the branch root's level is 0, else its row-1 parent index

This section computes all three and puts them together:

    branch_parent  the branch root's row-0 parent EXISTS and lies on the spine — everything
                   between the spine and the branch is deeper than the branch root
                   (§33's `hmid_of_blocks`), so it cannot be the parent, and column 0 can
    branch_deep    every other column of the branch is deeper than `p + 1` (§41's side
                   condition, from `spine_depth_ge` and the branch being a block)
    branch_lvl_par §35's `fpar_one_spine'`, with `u ≤ p + 1` supplied by `LvlOKb` at the
                   branch root and §39's level = index at `p`
    brF_getD / firstNodes_at / joints_at
                   the three scans, read off §30's `brF_blocks` and §33's `firstNodes_getD`
                   and `joints_getD`

and the conclusion is that

    branch_arg    NJ = psM (setRoot (p + 1) bJ)          — §41's matrix, exactly
    branch_shift  jnJ - nJ = p + 1 - (branch root's level)

Both cases of the `if` collapse into one statement (`branch_if`: the `if` equals `u - 1`,
where `u = 0` gives `-1` and `u ≥ 1` gives the row-1 parent), which is why `branch_arg` and
`branch_shift` have no case split left in them. -/

section
open Trans.Recal


/-! ### 枝の根の親は対角の上 -/

theorem branch_parent (X : Matrix) (tr J s : Nat) (hblk : BlkG X)
    (hJ : J < (blocks (X.drop (tr + 1))).length)
    (hs : s = tr + 1 + ((((blocks (X.drop (tr + 1))).take J).flatten).length))
    (hslen : s < X.length)
    (hroot : ent X s 0 = ent ((blocks (X.drop (tr + 1))).getD J []) 0 0) :
    ∃ p, parent X 0 s = some p ∧ p ≤ tr ∧ ent X p 0 < ent X s 0 := by
  have hs0 : 0 < s := by omega
  have hdeep : ent X 0 0 < ent X s 0 := hblk.2 s hs0 hslen
  have hmem : 0 ∈ (List.range s).filter (fun q => decide (ent X q 0 < ent X s 0)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hs0, decide_eq_true hdeep⟩
  cases hp : parent X 0 s with
  | none =>
    exfalso
    have hnil : ((List.range s).filter (fun q => decide (ent X q 0 < ent X s 0))) = [] :=
      List.max?_eq_none_iff.mp hp
    rw [hnil] at hmem
    exact absurd hmem (by simp)
  | some p =>
    have hpm := (List.max?_eq_some_iff.mp hp).1
    have hps : p < s := List.mem_range.mp (List.mem_filter.mp hpm).1
    have hplt : ent X p 0 < ent X s 0 := of_decide_eq_true (List.mem_filter.mp hpm).2
    refine ⟨p, rfl, ?_, hplt⟩
    rcases Nat.lt_or_ge tr p with hcon | hok
    · exfalso
      have hmid := hmid_of_blocks X tr J hJ p hcon (by omega)
      rw [← hroot] at hmid
      omega
    · exact hok

/-- 枝のどの列も `p + 1` より深い — 取り替えても根が一番浅い。 -/
theorem branch_deep (X Bk : Matrix) (tr s p : Nat) (h0d : ent X 0 0 = 0)
    (hrun : ∀ j, j < tr → ent X j 0 < ent X (j + 1) 0)
    (hptr : p ≤ tr) (hroot : ent X s 0 = ent Bk 0 0)
    (hplt : ent X p 0 < ent X s 0) (hblkBk : BlkG Bk) :
    ∀ q, 0 < q → q < Bk.length → p + 1 < ent Bk q 0 := by
  intro q hq hqlen
  have h1 := spine_depth_ge X tr h0d hrun p hptr
  have h2 := hblkBk.2 q hq hqlen
  omega

/-! ### 行 1 の親 -/

theorem branch_lvl_par (X : Matrix) (tr s p u : Nat) (h0l : ent X 0 1 = 0)
    (hlvl : LvlOKb X = true) (htr : tr < X.length)
    (hrun : ∀ j, j < tr → ent X j 0 < ent X (j + 1) 0 ∧ ent X j 1 < ent X (j + 1) 1)
    (hslen : s < X.length) (hpar : parent X 0 s = some p) (hptr : p ≤ tr)
    (hu : 1 ≤ u) (hlvls : ent X s 1 = u) :
    fpar (psM X) 1 ((s : Nat) : Int) 0 = ((u - 1 : Nat) : Int) := by
  refine fpar_one_spine' X tr u p s (fun j hj => (hrun j hj).1)
    (spine_lvl X tr h0l hlvl htr hrun) hu htr hslen ?_ hptr ?_ hlvls
  · rw [fpar0_eq_parent X s hslen, hpar]
  · have h1 := lvlOKb_at X hlvl s p hslen hpar
    have h2 := spine_lvl X tr h0l hlvl htr hrun p hptr
    omega

/-! ### 走査が返す 3 つの値 -/

theorem brF_getD (X : Matrix) (J : Nat) (hpos : 0 < X.length)
    (hJ : J < (blocks (X.drop (runLen X + 1))).length) :
    (brF (psM X)).getD J [] = psM ((blocks (X.drop (runLen X + 1))).getD J []) := by
  rw [brF_blocks X hpos]
  exact getD_map_lt psM _ [] [] J hJ

theorem brF_len (X : Matrix) (hpos : 0 < X.length) :
    (brF (psM X)).length = (blocks (X.drop (runLen X + 1))).length := by
  rw [brF_blocks X hpos, List.length_map]

theorem brF_take_len (X : Matrix) (J : Nat) (hpos : 0 < X.length) :
    ((((brF (psM X)).take J).flatten).length)
      = ((((blocks (X.drop (runLen X + 1))).take J).flatten).length) := by
  rw [brF_blocks X hpos, ← List.map_take, ← psM_flatten, psM_len]

theorem firstNodes_at (X : Matrix) (J s : Nat) (hpos : 0 < X.length)
    (hJ : J ≤ (blocks (X.drop (runLen X + 1))).length)
    (hs : s = runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)) :
    (firstNodes (psM X)).getD J 0 = ((s : Nat) : Int) := by
  rw [firstNodes_getD (psM X) J (by rw [brF_len X hpos]; exact hJ),
    trMax_runLen X hpos, brF_take_len X J hpos, hs]
  omega

theorem joints_at (X : Matrix) (J s p : Nat) (hpos : 0 < X.length)
    (hJ : J < (blocks (X.drop (runLen X + 1))).length)
    (hs : s = runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length))
    (hslen : s < X.length) (hpar : parent X 0 s = some p) :
    (joints (psM X)).getD J 0 = ((p : Nat) : Int) := by
  rw [joints_getD (psM X) J (by rw [brF_len X hpos]; exact hJ),
    firstNodes_at X J s hpos (by omega) hs, fpar_zero, fpar0_eq_parent X s hslen, hpar]

/-! ### 枝へ渡すもの -/

/-- **`if` の値は枝の根の段から 1 を引いたもの。** -/
theorem branch_if (X Bk : Matrix) (J s p u : Nat) (hpos : 0 < X.length)
    (hJ : J < (blocks (X.drop (runLen X + 1))).length)
    (hBk : (blocks (X.drop (runLen X + 1))).getD J [] = Bk)
    (hs : s = runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length))
    (hslen : s < X.length) (hpar : parent X 0 s = some p) (hptr : p ≤ runLen X)
    (h0l : ent X 0 1 = 0) (hlvl : LvlOKb X = true) (htrlt : runLen X < X.length)
    (hu : ent Bk 0 1 = u) (hlvls : ent X s 1 = u) :
    (if gp1 ((brF (psM X)).getD J []) 0 == 0 then (-1 : Int)
     else fpar (psM X) 1 ((firstNodes (psM X)).getD J 0) 0) = ((u : Nat) : Int) - 1 := by
  have hbr : (brF (psM X)).getD J [] = psM Bk := by rw [brF_getD X J hpos hJ, hBk]
  have hg1 : gp1 (psM Bk) 0 = ((u : Nat) : Int) := by
    have hh : gp1 (psM Bk) 0 = ((ent Bk 0 1 : Nat) : Int) := psM_gp1 Bk 0
    rw [hh, hu]
  rw [hbr, hg1]
  cases u with
  | zero =>
    rw [show ((((0 : Nat) : Int)) == 0) = true from rfl]
    simp only [if_true]
    rfl
  | succ w =>
    rw [show ((((w + 1 : Nat) : Int)) == 0) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    rw [firstNodes_at X J s hpos (by omega) hs,
      branch_lvl_par X (runLen X) s p (w + 1) h0l hlvl htrlt (runLen_run X hpos) hslen
        hpar hptr (by omega) hlvls]
    omega

/-- **畳み込みが枝へ渡す行列は、その枝の根の深さを `p + 1` に取り替えたもの。** -/
theorem branch_arg (X : Matrix) (c : Col) (cs : Matrix) (J s p u : Nat) (hpos : 0 < X.length)
    (hJ : J < (blocks (X.drop (runLen X + 1))).length)
    (hBk : (blocks (X.drop (runLen X + 1))).getD J [] = c :: cs)
    (hs : s = runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length))
    (hslen : s < X.length) (hpar : parent X 0 s = some p) (hptr : p ≤ runLen X)
    (h0l : ent X 0 1 = 0) (hlvl : LvlOKb X = true) (htrlt : runLen X < X.length)
    (hu : ent (c :: cs) 0 1 = u) (hlvls : ent X s 1 = u) :
    (((joints (psM X)).getD J 0 + 1,
      (if gp1 ((brF (psM X)).getD J []) 0 == 0 then (-1 : Int)
       else fpar (psM X) 1 ((firstNodes (psM X)).getD J 0) 0) + 1)
        :: derp ((brF (psM X)).getD J []))
      = psM (setRoot (p + 1) (c :: cs)) := by
  have hbr : (brF (psM X)).getD J [] = psM (c :: cs) := by rw [brF_getD X J hpos hJ, hBk]
  rw [branch_if X (c :: cs) J s p u hpos hJ hBk hs hslen hpar hptr h0l hlvl htrlt hu hlvls,
    joints_at X J s p hpos hJ hs hslen hpar, hbr, psM_setRoot p.succ c cs, hu,
    show ((p : Nat) : Int) + 1 = ((p + 1 : Nat) : Int) from by omega,
    show ((u : Nat) : Int) - 1 + 1 = ((u : Nat) : Int) from by omega]

/-- 平行移動の量。 -/
theorem branch_shift (X Bk : Matrix) (J s p u : Nat) (hpos : 0 < X.length)
    (hJ : J < (blocks (X.drop (runLen X + 1))).length)
    (hBk : (blocks (X.drop (runLen X + 1))).getD J [] = Bk)
    (hs : s = runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length))
    (hslen : s < X.length) (hpar : parent X 0 s = some p) (hptr : p ≤ runLen X)
    (h0l : ent X 0 1 = 0) (hlvl : LvlOKb X = true) (htrlt : runLen X < X.length)
    (hu : ent Bk 0 1 = u) (hlvls : ent X s 1 = u) :
    (joints (psM X)).getD J 0
        - (if gp1 ((brF (psM X)).getD J []) 0 == 0 then (-1 : Int)
           else fpar (psM X) 1 ((firstNodes (psM X)).getD J 0) 0)
      = ((p : Nat) : Int) + 1 - ((u : Nat) : Int) := by
  rw [branch_if X Bk J s p u hpos hJ hBk hs hslen hpar hptr h0l hlvl htrlt hu hlvls,
    joints_at X J s p hpos hJ hs hslen hpar]
  omega

end

/-! ## §44 THE FOLD

Everything the fold needs is now on the table, so this section runs it.

First the two facts that let the induction dispatch its cases at all.  `block_end_le` says a
block sits inside the matrix it came from — the offset plus its length is within range, which is
what `pieceList_nrm` and `anc0_blk` both want.  `not_prin_of_blocks` says two blocks or more
means NOT principal: the second block's root is no deeper than column 0 (§30's `blocks_root_le`),
and §22's `isAnc_false_of_flat` turns any such column into a refutation of principality.  With it
the induction can split on the number of blocks instead of on `isPrincipalP`.

`lvlOKb_sub` is the inheritance the recursion needs in the other direction: a block of a `LvlOKb`
matrix is `LvlOKb`, because §38's `parent_in_blk` says the parent of an inner column is the same
column seen from inside the block, and the level condition is then the one already assumed.

Then `redN_fold`.  With `red_fold_to` (§35) the answer is `jjSeq 0 tr ++ cs.flatten` for whatever
`cs` makes each term come out right, and §42 says the target `nrmBlk X` has exactly that shape
with `cs = pieceList (nrmG X) (tr + 1) (blocks (X.drop (tr + 1)))`.  So the whole proof is the
per-branch check, and that is §41 and §43 meeting:

    §43 branch_arg    the argument is `psM (setRoot (p + 1) Bk)`
    §43 branch_shift  the translation is `p + 1 - (branch root's level)`
    IH                that argument is shorter than `X`, is a block, and is `LvlOKb`
    §41 nrmBlk_setRoot  so the recursive answer is `nrmBlk Bk` — the root depth washes out
    §42 pieceList_nrm   and the target piece is `nrmBlk Bk` translated by `anc0 X s - level`
    §38 anc0_succ + §39 spine_anc0   and `anc0 X s = p + 1`, which is the same translation

The induction hypothesis is stated for every shorter block, not for the branches specifically —
that is what makes it usable, since `setRoot` changes the matrix. -/

section
open Trans.Recal


theorem drop_eq_getD_cons {γ : Type _} (d : γ) : ∀ (Bs : List γ) (J : Nat), J < Bs.length →
    Bs.drop J = Bs.getD J d :: Bs.drop (J + 1)
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: rest, K + 1, h => by
      have hK : K < rest.length := by
        simp at h
        omega
      show rest.drop K = rest.getD K d :: rest.drop (K + 1)
      exact drop_eq_getD_cons d rest K hK

theorem flatten_single (Bk : Matrix) : ([Bk] : List Matrix).flatten = Bk := by
  show Bk ++ ([] : List Matrix).flatten = Bk
  rw [show ([] : List Matrix).flatten = ([] : Matrix) from rfl, List.append_nil]

/-- `J` 番目のブロックまでの長さ。 -/
theorem take_succ_flatten_len (Bs : List Matrix) (J : Nat) (hJ : J < Bs.length) :
    (((Bs.take (J + 1)).flatten).length)
      = (((Bs.take J).flatten).length) + ((Bs.getD J []).length) := by
  have hg : Bs.getD J [] = Bs[J] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ]
    rfl
  rw [hg, List.take_add_one, List.getElem?_eq_getElem hJ]
  show ((Bs.take J ++ [Bs[J]]).flatten).length = ((Bs.take J).flatten).length + (Bs[J]).length
  rw [List.flatten_append, List.length_append, flatten_single]

/-- ブロックはその行列の中に収まる。 -/
theorem block_end_le (Bs : List Matrix) (J : Nat) (hJ : J < Bs.length) :
    (((Bs.take J).flatten).length) + ((Bs.getD J []).length) ≤ Bs.flatten.length := by
  rw [← take_flatten_prefix Bs J, List.length_append,
    drop_eq_getD_cons ([] : Matrix) Bs J hJ]
  show _ ≤ _ + (Bs.getD J [] ++ ((Bs.drop (J + 1)).flatten)).length
  rw [List.length_append]
  omega

theorem getD_mem_list {γ : Type _} (l : List γ) (d : γ) (i : Nat) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- **ブロックが 2 つ以上なら principal ではない。** -/
theorem not_prin_of_blocks (X : Matrix) (h2 : 2 ≤ (blocks X).length) :
    isPrincipalP (psM X) = false := by
  have hfl : (blocks X).flatten = X := blocks_flatten X.length X (Nat.le_refl _)
  have hblk0 : BlkG ((blocks X).getD 0 []) :=
    blocks_blkG X.length X (Nat.le_refl _) _ (getD_mem_list (blocks X) [] 0 (by omega))
  have hblk1 : BlkG ((blocks X).getD 1 []) :=
    blocks_blkG X.length X (Nat.le_refl _) _ (getD_mem_list (blocks X) [] 1 (by omega))
  have h00 : (((blocks X).take 0).flatten).length = 0 := rfl
  have hr : (((blocks X).take 1).flatten).length = ((blocks X).getD 0 []).length := by
    rw [take_succ_flatten_len (blocks X) 0 (by omega)]
    omega
  have hend1 := block_end_le (blocks X) 1 (by omega)
  rw [hfl] at hend1
  have hroot : ent X ((((blocks X).take 1).flatten).length) 0
      = ent ((blocks X).getD 1 []) 0 0 := by
    have hb := ent_flatten_block (blocks X) 1 (by omega) 0 0 hblk1.1
    rw [hfl, show (((blocks X).take 1).flatten).length + 0
      = (((blocks X).take 1).flatten).length from by omega] at hb
    exact hb
  have hle := blocks_root_le X.length X (Nat.le_refl _) 1 (by omega)
  have hlen0 := hblk0.1
  have hlen1 := hblk1.1
  have hfalse : isAnc (psM X) 0 (lenI (psM X) - 1) 0 = false :=
    isAnc_false_of_flat X ((((blocks X).take 1).flatten).length)
      (by omega) (by omega) (by omega) (by omega)
  refine Bool.eq_false_iff.mpr (fun hcon => ?_)
  have hdef : isPrincipalP (psM X)
      = (!isZeroP (psM X) && isAnc (psM X) 0 (lenI (psM X) - 1) 0) := rfl
  rw [hdef, hfalse, Bool.and_false] at hcon
  exact absurd hcon (by simp)

/-- ブロックは `LvlOKb` を受け継ぐ。 -/
theorem lvlOKb_sub (X Bk : Matrix) (s : Nat) (hlvl : LvlOKb X = true)
    (hpos : ∀ i, i < Bk.length → ent X (s + i) 0 = ent Bk i 0)
    (hlv : ∀ i, i < Bk.length → ent X (s + i) 1 = ent Bk i 1)
    (hend : s + Bk.length ≤ X.length) : LvlOKb Bk = true := by
  show ((List.range Bk.length).all _) = true
  refine List.all_eq_true.mpr (fun i hi => ?_)
  have hi' : i < Bk.length := List.mem_range.mp hi
  cases hp : parent Bk 0 i with
  | none => rfl
  | some q =>
    have hqi := parent0_lt Bk i q hp
    have hX := parent_in_blk X s Bk i q hpos hi' hp
    have hle := lvlOKb_at X hlvl (s + i) (s + q) (by omega) hX
    rw [hlv i hi', hlv q (by omega)] at hle
    exact decide_eq_true hle

/-! ### 畳み込み -/

/-- **ブロック 1 つ・根は深さ 0 段 0・走りが尽きない場合。** -/
theorem redN_fold (f : Nat) (X : Matrix) (bnd : Nat) (hblk : BlkG X) (hlvl : LvlOKb X = true)
    (h0d : ent X 0 0 = 0) (h0l : ent X 0 1 = 0) (hlen : 1 < X.length)
    (hstop : runLen X + 1 < X.length)
    (hbnd : ∀ J, J < (blocks (X.drop (runLen X + 1))).length →
              ((blocks (X.drop (runLen X + 1))).getD J []).length < bnd)
    (ih : ∀ Y : Matrix, Y.length < bnd → BlkG Y → LvlOKb Y = true →
            red f (psM Y) = nrmBlk Y) :
    red (f + 1) (psM X) = nrmBlk X := by
  have hpos : 0 < X.length := by omega
  have htrlt : runLen X < X.length := runLen_lt X hpos
  have hrun := runLen_run X hpos
  have hzero : isZeroP (psM X) = false := by
    show ((psM X).length == 1 && _) = false
    rw [show ((psM X).length == 1) = false from by
      rw [psM_len]; exact decide_eq_false (by omega)]
    rfl
  have hprin : isPrincipalP (psM X) = true := prin_of_deep X hlen hblk.2
  have hg0 : gp0 (psM X) 0 = 0 := by
    have hh : gp0 (psM X) 0 = ((ent X 0 0 : Nat) : Int) := psM_gp0 X 0
    rw [hh, h0d]; rfl
  have hg1 : gp1 (psM X) 0 = 0 := by
    have hh : gp1 (psM X) 0 = ((ent X 0 1 : Nat) : Int) := psM_gp1 X 0
    rw [hh, h0l]; rfl
  have hne : ((((runLen X : Nat)) : Int) == lenI (psM X) - 1) = false := by
    rw [lenI_psM]
    refine Bool.eq_false_iff.mpr (fun hcon => ?_)
    have := eq_of_beq hcon
    omega
  have hflat : (blocks (X.drop (runLen X + 1))).flatten = X.drop (runLen X + 1) :=
    blocks_flatten (X.drop (runLen X + 1)).length (X.drop (runLen X + 1)) (Nat.le_refl _)
  have hcslen : (brF (psM X)).length
      = (pieceList (nrmG X) (runLen X + 1) (blocks (X.drop (runLen X + 1)))).length := by
    rw [brF_len X hpos, pieceList_length]
  rw [red_fold_to (psM X) f ((runLen X : Nat) : Int)
      (pieceList (nrmG X) (runLen X + 1) (blocks (X.drop (runLen X + 1))))
      hzero hprin hg0 hg1 (trMax_runLen X hpos) hne hcslen ?_,
    ← nrmBlk_diag_split X (runLen X) h0l hlvl htrlt hrun]
  -- 各枝
  intro J hJcs
  have hJ : J < (blocks (X.drop (runLen X + 1))).length := by
    rw [pieceList_length] at hJcs
    exact hJcs
  have hBkblk : BlkG ((blocks (X.drop (runLen X + 1))).getD J []) :=
    blocks_blkG (X.drop (runLen X + 1)).length (X.drop (runLen X + 1)) (Nat.le_refl _) _
      (getD_mem_list _ [] J hJ)
  have hbe := block_end_le (blocks (X.drop (runLen X + 1))) J hJ
  rw [hflat, List.length_drop] at hbe
  have hend : runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)
      + ((blocks (X.drop (runLen X + 1))).getD J []).length ≤ X.length := by omega
  have hlen0 := hBkblk.1
  have hslen : runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)
      < X.length := by omega
  have hpe : ∀ i, i < ((blocks (X.drop (runLen X + 1))).getD J []).length → ∀ y,
      ent X (runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length) + i) y
        = ent ((blocks (X.drop (runLen X + 1))).getD J []) i y :=
    fun i hi y => ent_brBlk X (runLen X) J hJ i y hi
  have hroot : ent X (runLen X + 1
        + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)) 0
      = ent ((blocks (X.drop (runLen X + 1))).getD J []) 0 0 := by
    have hb := hpe 0 hlen0 0
    rw [show runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length) + 0
      = runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)
      from by omega] at hb
    exact hb
  have hlvls : ent X (runLen X + 1
        + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)) 1
      = ent ((blocks (X.drop (runLen X + 1))).getD J []) 0 1 := by
    have hb := hpe 0 hlen0 1
    rw [show runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length) + 0
      = runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)
      from by omega] at hb
    exact hb
  obtain ⟨p, hpar, hptr, hplt⟩ := branch_parent X (runLen X) J
    (runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length))
    hblk hJ rfl hslen hroot
  have hlo := branch_deep X ((blocks (X.drop (runLen X + 1))).getD J []) (runLen X)
    (runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)) p
    h0d (fun j hj => (hrun j hj).1) hptr hroot hplt hBkblk
  have hlvlBk : LvlOKb ((blocks (X.drop (runLen X + 1))).getD J []) = true :=
    lvlOKb_sub X _ _ hlvl (fun i hi => hpe i hi 0) (fun i hi => hpe i hi 1) (by omega)
  have hanc : anc0 X (runLen X + 1
      + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length)) = p + 1 := by
    rw [anc0_succ X _ p hslen hpar,
      spine_anc0 X (runLen X) htrlt hrun p hptr]
  -- 帰納法の仮定を枝に当てる
  cases hBk : (blocks (X.drop (runLen X + 1))).getD J [] with
  | nil => exact absurd (hBk ▸ hlen0) (by simp)
  | cons c cs =>
    rw [branch_arg X c cs J
        (runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length))
        p (ent (c :: cs) 0 1) hpos hJ hBk rfl hslen hpar hptr h0l hlvl htrlt rfl
        (by rw [hlvls, hBk]),
      branch_shift X (c :: cs) J
        (runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length))
        p (ent (c :: cs) 0 1) hpos hJ hBk rfl hslen hpar hptr h0l hlvl htrlt rfl
        (by rw [hlvls, hBk]),
      ih (setRoot (p + 1) (c :: cs))
        (by
          rw [setRoot_length]
          have hb := hbnd J hJ
          rw [hBk] at hb
          omega)
        (blkG_setRoot (p + 1) (c :: cs) (hBk ▸ hBkblk) (by rw [← hBk]; exact hlo))
        (lvlOKb_setRoot (p + 1) (c :: cs) (hBk ▸ hBkblk) (by rw [← hBk]; exact hlo)
          (hBk ▸ hlvlBk)),
      nrmBlk_setRoot (p + 1) (c :: cs) (hBk ▸ hBkblk) (by rw [← hBk]; exact hlo),
      pieceList_nrm X (c :: cs)
        (runLen X + 1 + ((((blocks (X.drop (runLen X + 1))).take J).flatten).length))
        (blocks (X.drop (runLen X + 1))) (runLen X + 1) J h0l hJ hBk rfl
        (fun i hi => by rw [← hBk] at hi ⊢; exact hpe i hi 0)
        (fun i hi => by rw [← hBk] at hi ⊢; exact hpe i hi 1)
        (hBk ▸ hBkblk) (by rw [hBk] at hend; omega),
      hanc, show ((p : Nat) : Int) + 1 = ((p + 1 : Nat) : Int) from by omega]

/-- 枝はもとの行列より短い — `redN_fold` を自分自身の長さで使う形。 -/
theorem redN_fold_self (f : Nat) (X : Matrix) (hblk : BlkG X) (hlvl : LvlOKb X = true)
    (h0d : ent X 0 0 = 0) (h0l : ent X 0 1 = 0) (hlen : 1 < X.length)
    (hstop : runLen X + 1 < X.length)
    (ih : ∀ Y : Matrix, Y.length < X.length → BlkG Y → LvlOKb Y = true →
            red f (psM Y) = nrmBlk Y) :
    red (f + 1) (psM X) = nrmBlk X := by
  refine redN_fold f X X.length hblk hlvl h0d h0l hlen hstop (fun J hJ => ?_) ih
  have hbe := block_end_le (blocks (X.drop (runLen X + 1))) J hJ
  rw [blocks_flatten (X.drop (runLen X + 1)).length (X.drop (runLen X + 1)) (Nat.le_refl _),
    List.length_drop] at hbe
  omega

end

/-! ## §45 THE OTHER TWO BRANCHES

`redN_diag` — the run covers the whole matrix.  `red` returns the diagonal (`red_jj`), and §39
already says the first `tr + 1` entries of the answer ARE the diagonal; here `tr + 1` is the
whole length, so the `take` is the identity.

`redN_head` — the root's level `u` is at least 1.  `red` prepends a diagonal of height `u`,
pushes the matrix down by `u`, reduces THAT, and then throws the diagonal away.  The prepended
matrix is `auxMat X = diagMat u ++ sh u X`, and this section establishes what it needs:

    blkG_auxMat / lvlOKb_auxMat   it is a block and it is in the class — `LvlOKb` survives
                                  because levels are untouched and parents are either the
                                  previous diagonal column or §38's `parent_in_blk`
    runLen_auxMat                 the run covers at least the prepended diagonal: depth and
                                  level both step by one along it, and at the junction the
                                  root of `X` is deeper (it was pushed down) and higher
                                  (its level is `u`, one more than `u - 1`)
    anc0_auxMat_hi                so tree depth below the junction is `u + (tree depth in X)`
    nrmBlk_auxMat_drop            hence dropping the first `u` entries of the answer for
                                  `auxMat X` gives exactly the answer for `X`

That last one is the point: `nrmM` puts a column at `root level + tree depth`, `X`'s root level
IS `u`, and `auxMat X`'s root level is 0 with `u` added to every tree depth below the junction —
the same numbers.  So the outer step is the identity: the translation `red` applies is
`-(gp0) + gp1` read at the junction, and both are `u` there, so it translates by zero.

`redN_block` is the two branches of the fold case packaged together (run covers everything, or
not), which is what the level-positive case calls on `auxMat X`.  Note the bound it passes is
`X.length`, NOT `(auxMat X).length` — `auxMat X` is longer than `X`, and the induction survives
only because its BRANCHES are shorter than `X`, which is what `runLen_auxMat` buys. -/

section
open Trans.Recal


/-! ### 走りが全部を覆う場合 -/

theorem redN_diag (f : Nat) (X : Matrix) (hblk : BlkG X) (hlvl : LvlOKb X = true)
    (h0d : ent X 0 0 = 0) (h0l : ent X 0 1 = 0) (hlen : 1 < X.length)
    (hcov : X.length ≤ runLen X + 1) :
    red (f + 1) (psM X) = nrmBlk X := by
  have hpos : 0 < X.length := by omega
  have htrlt := runLen_lt X hpos
  have hzero : isZeroP (psM X) = false := by
    show ((psM X).length == 1 && _) = false
    rw [show ((psM X).length == 1) = false from by
      rw [psM_len]; exact decide_eq_false (by omega)]
    rfl
  have hprin : isPrincipalP (psM X) = true := prin_of_deep X hlen hblk.2
  have hg0 : gp0 (psM X) 0 = 0 := by
    have hh : gp0 (psM X) 0 = ((ent X 0 0 : Nat) : Int) := psM_gp0 X 0
    rw [hh, h0d]; rfl
  have hg1 : gp1 (psM X) 0 = 0 := by
    have hh : gp1 (psM X) 0 = ((ent X 0 1 : Nat) : Int) := psM_gp1 X 0
    rw [hh, h0l]; rfl
  have hlenI : lenI (psM X) - 1 = ((runLen X : Nat) : Int) := by
    rw [lenI_psM]; omega
  rw [Rows.Ladder.red_jj (psM X) f hzero hprin hg0 hg1
      (by rw [trMax_runLen X hpos, hlenI]), hlenI,
    ← nrmBlk_take X (runLen X) h0l hlvl htrlt (runLen_run X hpos),
    List.take_of_length_le (by rw [nrmBlk_length]; omega)]

/-- ブロック 1 つ・根は深さ 0 段 0 — 走りが尽きるかどうかで 2 つに分かれる。 -/
theorem redN_block (f : Nat) (Z : Matrix) (bnd : Nat) (hblk : BlkG Z) (hlvl : LvlOKb Z = true)
    (h0d : ent Z 0 0 = 0) (h0l : ent Z 0 1 = 0) (hlen : 1 < Z.length)
    (hbnd : ∀ J, J < (blocks (Z.drop (runLen Z + 1))).length →
              ((blocks (Z.drop (runLen Z + 1))).getD J []).length < bnd)
    (ih : ∀ Y : Matrix, Y.length < bnd → BlkG Y → LvlOKb Y = true →
            red f (psM Y) = nrmBlk Y) :
    red (f + 1) (psM Z) = nrmBlk Z := by
  rcases Nat.lt_or_ge (runLen Z + 1) Z.length with h | h
  · exact redN_fold f Z bnd hblk hlvl h0d h0l hlen h hbnd ih
  · exact redN_diag f Z hblk hlvl h0d h0l hlen h

/-! ### 深さを一斉に上げる -/

theorem sh_length (e : Nat) (X : Matrix) : (sh e X).length = X.length := List.length_map ..

theorem ent_sh0 (e : Nat) (X : Matrix) (i : Nat) (hi : i < X.length) :
    ent (sh e X) i 0 = ent X i 0 + e := by
  show ((X.map (shc e)).getD i []).getD 0 0 = _
  rw [getD_map_lt _ X [] [] i hi]
  rfl

theorem ent_sh1 (e : Nat) (X : Matrix) (i : Nat) (hi : i < X.length) :
    ent (sh e X) i 1 = ent X i 1 := by
  show ((X.map (shc e)).getD i []).getD 1 0 = _
  rw [getD_map_lt _ X [] [] i hi]
  exact getD_drop_one (X.getD i [])

theorem parent_sh (e : Nat) (X : Matrix) :
    ∀ i, i < X.length → parent (sh e X) 0 i = parent X 0 i := by
  intro i0 hi0
  refine parent_congr (sh e X) X (fun p i hpi hi => ?_) i0 (by rw [sh_length]; exact hi0)
  rw [sh_length] at hi
  rw [ent_sh0 e X p (by omega), ent_sh0 e X i hi]
  by_cases hc : ent X p 0 < ent X i 0
  · rw [decide_eq_true (show ent X p 0 + e < ent X i 0 + e from by omega), decide_eq_true hc]
  · rw [decide_eq_false (show ¬(ent X p 0 + e < ent X i 0 + e) from by omega),
      decide_eq_false hc]

theorem anc0_sh (e : Nat) (X : Matrix) : ∀ i, i < X.length → anc0 (sh e X) i = anc0 X i := by
  intro i hi
  exact anc0_congr (sh e X) X (sh_length e X)
    (fun j hj => parent_sh e X j (by rw [sh_length] at hj; exact hj))
    i (by rw [sh_length]; exact hi)

theorem blkG_sh (e : Nat) (X : Matrix) (h : BlkG X) : BlkG (sh e X) := by
  refine ⟨by rw [sh_length]; exact h.1, ?_⟩
  intro p hp hplen
  rw [sh_length] at hplen
  rw [ent_sh0 e X 0 h.1, ent_sh0 e X p hplen]
  have := h.2 p hp hplen
  omega

/-! ### 対角の行列 -/

theorem diagMat_length (k : Nat) : (diagMat k).length = k := by
  show ((List.range k).map _).length = _
  rw [List.length_map, List.length_range]

theorem ent_diagMat (k i y : Nat) (hi : i < k) (hy : y < 2) : ent (diagMat k) i y = i := by
  show (((List.range k).map (fun j => [j, j])).getD i []).getD y 0 = _
  rw [getD_map_range k (fun j => [j, j]) [] i hi]
  match y, hy with
  | 0, _ => rfl
  | 1, _ => rfl

theorem psM_diagMat (k : Nat) (hk : 1 ≤ k) :
    psM (diagMat k) = jjSeq 0 (((k : Nat) : Int) - 1) := by
  show ((List.range k).map (fun j => [j, j])).map
      (fun c => (((c.getD 0 0 : Nat) : Int), ((c.getD 1 0 : Nat) : Int))) = _
  rw [List.map_map,
    show ((k : Nat) : Int) - 1 = (((k - 1 : Nat)) : Int) from by omega,
    jjSeq_zero (k - 1), show k - 1 + 1 = k from by omega]
  rfl

/-! ### 前置きした対角のついた行列 -/

theorem auxMat_length (X : Matrix) : (auxMat X).length = ent X 0 1 + X.length := by
  show (diagMat (ent X 0 1) ++ sh (ent X 0 1) X).length = _
  rw [List.length_append, diagMat_length, sh_length]

theorem ent_auxMat_lo (X : Matrix) (i y : Nat) (hi : i < ent X 0 1) (hy : y < 2) :
    ent (auxMat X) i y = i := by
  show ent (diagMat (ent X 0 1) ++ sh (ent X 0 1) X) i y = _
  rw [ent_append_left _ _ i y (by rw [diagMat_length]; exact hi), ent_diagMat _ i y hi hy]

theorem ent_auxMat_hi (X : Matrix) (k y : Nat) :
    ent (auxMat X) (ent X 0 1 + k) y = ent (sh (ent X 0 1) X) k y := by
  show ent (diagMat (ent X 0 1) ++ sh (ent X 0 1) X) (ent X 0 1 + k) y = _
  rw [ent_append _ _ _ y (by rw [diagMat_length]; omega), diagMat_length,
    show ent X 0 1 + k - ent X 0 1 = k from by omega]

theorem blkG_auxMat (X : Matrix) (hu : 1 ≤ ent X 0 1) : BlkG (auxMat X) := by
  refine ⟨by rw [auxMat_length]; omega, ?_⟩
  intro p hp hplen
  rw [auxMat_length] at hplen
  rw [ent_auxMat_lo X 0 0 (by omega) (by omega)]
  rcases Nat.lt_or_ge p (ent X 0 1) with hlo | hhi
  · rw [ent_auxMat_lo X p 0 hlo (by omega)]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, p = ent X 0 1 + k := ⟨p - ent X 0 1, by omega⟩
    rw [ent_auxMat_hi X k 0, ent_sh0 _ X k (by omega)]
    omega

/-- 前置きした対角の上の親は 1 つ左。 -/
theorem parent_auxMat_lo (X : Matrix) (hblk : BlkG X) :
    ∀ j, 1 ≤ j → j ≤ ent X 0 1 → parent (auxMat X) 0 j = some (j - 1) := by
  intro j hj1 hju
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [show k + 1 - 1 = k from by omega]
  refine parent_succ_of_lt (auxMat X) k ?_
  rw [ent_auxMat_lo X k 0 (by omega) (by omega)]
  rcases Nat.lt_or_ge (k + 1) (ent X 0 1) with hlo | hhi
  · rw [ent_auxMat_lo X (k + 1) 0 hlo (by omega)]
    omega
  · rw [show k + 1 = ent X 0 1 + 0 from by omega, ent_auxMat_hi X 0 0,
      ent_sh0 _ X 0 hblk.1]
    omega

/-- 前置きした対角の下では、親はもとの行列の親を `u` だけずらしたもの。 -/
theorem parent_auxMat_hi (X : Matrix) (k q : Nat) (hk : k < X.length)
    (hq : parent X 0 k = some q) :
    parent (auxMat X) 0 (ent X 0 1 + k) = some (ent X 0 1 + q) := by
  refine parent_in_blk (auxMat X) (ent X 0 1) (sh (ent X 0 1) X) k q
    (fun i _ => ent_auxMat_hi X i 0) (by rw [sh_length]; exact hk) ?_
  rw [parent_sh (ent X 0 1) X k hk]
  exact hq

theorem lvlOKb_auxMat (X : Matrix) (hu : 1 ≤ ent X 0 1) (hblk : BlkG X)
    (hlvl : LvlOKb X = true) : LvlOKb (auxMat X) = true := by
  show ((List.range (auxMat X).length).all _) = true
  refine List.all_eq_true.mpr (fun i hi => ?_)
  have hi' : i < ent X 0 1 + X.length := by
    have := List.mem_range.mp hi
    rw [auxMat_length] at this
    exact this
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [show parent (auxMat X) 0 0 = none from rfl]
  · rcases Nat.lt_or_ge i (ent X 0 1 + 1) with hlo | hhi
    · rw [parent_auxMat_lo X hblk i hipos (by omega)]
      show decide (ent (auxMat X) i 1 ≤ ent (auxMat X) (i - 1) 1 + 1) = true
      rw [ent_auxMat_lo X (i - 1) 1 (by omega) (by omega)]
      rcases Nat.lt_or_ge i (ent X 0 1) with h2 | h2
      · rw [ent_auxMat_lo X i 1 h2 (by omega)]
        exact decide_eq_true (by omega)
      · rw [show i = ent X 0 1 + 0 from by omega, ent_auxMat_hi X 0 1,
          ent_sh1 _ X 0 hblk.1]
        exact decide_eq_true (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k, i = ent X 0 1 + k := ⟨i - ent X 0 1, by omega⟩
      have hkpos : 0 < k := by omega
      obtain ⟨q, hq⟩ := parent_blk_some X k hkpos (by omega) hblk
      have hqk := parent0_lt X k q hq
      rw [parent_auxMat_hi X k q (by omega) hq]
      show decide (ent (auxMat X) (ent X 0 1 + k) 1
        ≤ ent (auxMat X) (ent X 0 1 + q) 1 + 1) = true
      rw [ent_auxMat_hi X k 1, ent_auxMat_hi X q 1, ent_sh1 _ X k (by omega),
        ent_sh1 _ X q (by omega)]
      exact decide_eq_true (lvlOKb_at X hlvl k q (by omega) hq)

/-! ### 走りは前置きした対角を最後まで走る -/

theorem runLen_ge (M : Matrix) (m : Nat) (hpos : 0 < M.length) (hm : m < M.length)
    (hcond : ∀ j, j < m → ent M j 0 < ent M (j + 1) 0 ∧ ent M j 1 < ent M (j + 1) 1) :
    m ≤ runLen M := by
  rcases Nat.lt_or_ge (runLen M) m with h | h
  · exfalso
    rcases runLen_stop M hpos with hstop | hstop
    · omega
    · exact hstop (hcond (runLen M) h)
  · exact h

theorem runLen_auxMat (X : Matrix) (hu : 1 ≤ ent X 0 1) (hblk : BlkG X) :
    ent X 0 1 ≤ runLen (auxMat X) := by
  have hlen0 := hblk.1
  refine runLen_ge (auxMat X) (ent X 0 1) (by rw [auxMat_length]; omega)
    (by rw [auxMat_length]; omega) (fun j hj => ?_)
  rcases Nat.lt_or_ge (j + 1) (ent X 0 1) with hlo | hhi
  · rw [ent_auxMat_lo X j 0 (by omega) (by omega), ent_auxMat_lo X (j + 1) 0 hlo (by omega),
      ent_auxMat_lo X j 1 (by omega) (by omega), ent_auxMat_lo X (j + 1) 1 hlo (by omega)]
    exact ⟨by omega, by omega⟩
  · rw [ent_auxMat_lo X j 0 (by omega) (by omega), ent_auxMat_lo X j 1 (by omega) (by omega),
      show j + 1 = ent X 0 1 + 0 from by omega, ent_auxMat_hi X 0 0, ent_auxMat_hi X 0 1,
      ent_sh0 _ X 0 hlen0, ent_sh1 _ X 0 hlen0]
    exact ⟨by omega, by omega⟩

/-! ### 前置きした対角の木 -/

theorem anc0_auxMat_lo (X : Matrix) (hblk : BlkG X) :
    ∀ j, j ≤ ent X 0 1 → anc0 (auxMat X) j = j :=
  anc0_spine (auxMat X) (ent X 0 1) (by rw [auxMat_length]; have := hblk.1; omega)
    (parent_auxMat_lo X hblk)

theorem anc0_auxMat_hi (X : Matrix) (hblk : BlkG X) (k : Nat)
    (hk : k < X.length) : anc0 (auxMat X) (ent X 0 1 + k) = ent X 0 1 + anc0 X k := by
  rw [anc0_blk (auxMat X) (ent X 0 1) (sh (ent X 0 1) X)
      (fun i _ => ent_auxMat_hi X i 0) (blkG_sh (ent X 0 1) X hblk)
      (by rw [auxMat_length, sh_length]; omega) k k (Nat.le_refl k)
      (by rw [sh_length]; exact hk),
    anc0_auxMat_lo X hblk (ent X 0 1) (Nat.le_refl _), anc0_sh (ent X 0 1) X k hk]

theorem nrmBlk_auxMat_drop (X : Matrix) (hu : 1 ≤ ent X 0 1) (hblk : BlkG X) :
    (nrmBlk (auxMat X)).drop (ent X 0 1) = nrmBlk X := by
  rw [nrmBlk_eq_map (auxMat X), auxMat_length,
    range_add_map (nrmG (auxMat X)) (ent X 0 1) X.length,
    drop_app_len _ _ (ent X 0 1) (by rw [List.length_map, List.length_range]),
    nrmBlk_eq_map X]
  refine List.map_congr_left (fun k hk => ?_)
  have hk' : k < X.length := List.mem_range.mp hk
  show (((ent (auxMat X) 0 1 + anc0 (auxMat X) (ent X 0 1 + k) : Nat) : Int),
        ((ent (auxMat X) (ent X 0 1 + k) 1 : Nat) : Int))
    = (((ent X 0 1 + anc0 X k : Nat) : Int), ((ent X k 1 : Nat) : Int))
  rw [ent_auxMat_lo X 0 1 (by omega) (by omega), anc0_auxMat_hi X hblk k hk',
    ent_auxMat_hi X k 1, ent_sh1 _ X k hk',
    show 0 + (ent X 0 1 + anc0 X k) = ent X 0 1 + anc0 X k from by omega]

/-! ### 答えの行列 -/

/-- `nrmBlk` を行列として書いたもの。 -/
def nrmMat (X : Matrix) : Matrix :=
  (List.range X.length).map (fun i => [ent X 0 1 + anc0 X i, ent X i 1])

theorem psM_nrmMat (X : Matrix) : psM (nrmMat X) = nrmBlk X := by
  show ((List.range X.length).map _).map _ = (List.range X.length).map _
  rw [List.map_map]
  rfl

theorem nrmMat_length (X : Matrix) : (nrmMat X).length = X.length := by
  show ((List.range X.length).map _).length = _
  rw [List.length_map, List.length_range]

theorem ent_nrmMat0 (X : Matrix) (i : Nat) (hi : i < X.length) :
    ent (nrmMat X) i 0 = ent X 0 1 + anc0 X i := by
  show (((List.range X.length).map (fun j => [ent X 0 1 + anc0 X j, ent X j 1])).getD i
    []).getD 0 0 = _
  rw [getD_map_range X.length _ [] i hi]
  rfl

theorem anc0_pos (X : Matrix) (hblk : BlkG X) (i : Nat) (hi : 0 < i) (hlen : i < X.length) :
    0 < anc0 X i := by
  obtain ⟨p, hp⟩ := parent_blk_some X i hi hlen hblk
  rw [anc0_succ X i p hlen hp]
  omega

theorem blkG_nrmMat (X : Matrix) (hblk : BlkG X) : BlkG (nrmMat X) := by
  refine ⟨by rw [nrmMat_length]; exact hblk.1, ?_⟩
  intro p hp hplen
  rw [nrmMat_length] at hplen
  rw [ent_nrmMat0 X 0 hblk.1, ent_nrmMat0 X p hplen, anc0_zero]
  have := anc0_pos X hblk p hp hplen
  omega

theorem prin_nrmBlk (X : Matrix) (hblk : BlkG X) (hlen : 1 < X.length) :
    isPrincipalP (nrmBlk X) = true := by
  rw [← psM_nrmMat X]
  exact prin_of_deep (nrmMat X) (by rw [nrmMat_length]; exact hlen) (blkG_nrmMat X hblk).2

/-! ### 小道具 -/

theorem getD_drop_zero {α : Type _} (L : List α) (d : α) (n : Nat) :
    (L.drop n).getD 0 d = L.getD n d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
    show n + 0 = n from by omega]

theorem incrFirst_zero : ∀ (L : PS), incrFirst L 0 = L
  | [] => rfl
  | c :: cs => by
      show ((c.1 + 0, c.2) :: incrFirst cs 0) = c :: cs
      rw [incrFirst_zero cs, show c.1 + 0 = c.1 from by omega]

/-! ### 根の段が 1 以上の場合 -/

theorem psM_auxMat (X : Matrix) (hu : 1 ≤ ent X 0 1) :
    psM (auxMat X) = jjSeq 0 (((ent X 0 1 : Nat) : Int) - 1)
      ++ incrFirst (psM X) ((ent X 0 1 : Nat) : Int) := by
  show psM (diagMat (ent X 0 1) ++ sh (ent X 0 1) X) = _
  rw [psM_append, psM_diagMat (ent X 0 1) hu, psM_sh (ent X 0 1) X]

/-- **根の段が 1 以上の場合。** 対角を前置きして畳み込み、頭を落とす。 -/
theorem redN_head (g : Nat) (X : Matrix) (hblk : BlkG X) (hlvl : LvlOKb X = true)
    (hu : 1 ≤ ent X 0 1) (hlen : 1 < X.length)
    (ih : ∀ Y : Matrix, Y.length < X.length → BlkG Y → LvlOKb Y = true →
            red g (psM Y) = nrmBlk Y) :
    red (g + 1 + 1) (psM X) = nrmBlk X := by
  have hlen0 := hblk.1
  have hzero : isZeroP (psM X) = false := by
    show ((psM X).length == 1 && _) = false
    rw [show ((psM X).length == 1) = false from by
      rw [psM_len]; exact decide_eq_false (by omega)]
    rfl
  have hprin : isPrincipalP (psM X) = true := prin_of_deep X hlen hblk.2
  have hgp1 : gp1 (psM X) 0 = ((ent X 0 1 : Nat) : Int) := psM_gp1 X 0
  have hg1ne : (gp1 (psM X) 0 == 0) = false := by
    rw [hgp1]
    refine Bool.eq_false_iff.mpr (fun hcon => ?_)
    have := eq_of_beq hcon
    omega
  -- 前置きした行列の `red`
  have haux : red (g + 1) (psM (auxMat X)) = nrmBlk (auxMat X) := by
    refine redN_block (g) (auxMat X) X.length (blkG_auxMat X hu)
      (lvlOKb_auxMat X hu hblk hlvl)
      (ent_auxMat_lo X 0 0 (by omega) (by omega))
      (ent_auxMat_lo X 0 1 (by omega) (by omega))
      (by rw [auxMat_length]; omega) (fun J hJ => ?_) ih
    have hbe := block_end_le (blocks ((auxMat X).drop (runLen (auxMat X) + 1))) J hJ
    rw [blocks_flatten ((auxMat X).drop (runLen (auxMat X) + 1)).length _ (Nat.le_refl _),
      List.length_drop, auxMat_length] at hbe
    have hge := runLen_auxMat X hu hblk
    omega
  rw [red_head_pos (psM X) (g + 1) hzero hprin hg1ne, hgp1, ← psM_auxMat X hu]
  show (if decide (((ent X 0 1 : Nat) : Int)
            ≤ lenI (red (g + 1) (psM (auxMat X))) - 1)
          && isPrincipalP ((red (g + 1) (psM (auxMat X))).drop
              (((ent X 0 1 : Nat) : Int)).toNat) then
          incrFirst ((red (g + 1) (psM (auxMat X))).drop (((ent X 0 1 : Nat) : Int)).toNat)
            (-(gp0 (red (g + 1) (psM (auxMat X))) ((ent X 0 1 : Nat) : Int))
              + gp1 (red (g + 1) (psM (auxMat X))) ((ent X 0 1 : Nat) : Int))
        else psM X) = nrmBlk X
  rw [haux, show (((ent X 0 1 : Nat) : Int)).toNat = ent X 0 1 from by omega,
    nrmBlk_auxMat_drop X hu hblk]
  have hgetu : (nrmBlk (auxMat X)).getD (ent X 0 1) ((0 : Int), (0 : Int))
      = (((ent X 0 1 : Nat) : Int), ((ent X 0 1 : Nat) : Int)) := by
    rw [← getD_drop_zero (nrmBlk (auxMat X)) ((0 : Int), (0 : Int)) (ent X 0 1),
      nrmBlk_auxMat_drop X hu hblk]
    show ((List.range X.length).map (nrmG X)).getD 0 ((0 : Int), (0 : Int)) = _
    rw [getD_map_range X.length (nrmG X) ((0 : Int), (0 : Int)) 0 (by omega)]
    show (((ent X 0 1 + anc0 X 0 : Nat) : Int), ((ent X 0 1 : Nat) : Int)) = _
    rw [anc0_zero X, show ent X 0 1 + 0 = ent X 0 1 from by omega]
  have hgp0N : gp0 (nrmBlk (auxMat X)) ((ent X 0 1 : Nat) : Int)
      = ((ent X 0 1 : Nat) : Int) := by
    show (if ((ent X 0 1 : Nat) : Int) < 0 then (0 : Int)
          else ((nrmBlk (auxMat X)).getD (((ent X 0 1 : Nat) : Int)).toNat (0, 0)).1) = _
    rw [if_neg (by omega), show (((ent X 0 1 : Nat) : Int)).toNat = ent X 0 1 from by omega,
      hgetu]
  have hgp1N : gp1 (nrmBlk (auxMat X)) ((ent X 0 1 : Nat) : Int)
      = ((ent X 0 1 : Nat) : Int) := by
    show (if ((ent X 0 1 : Nat) : Int) < 0 then (0 : Int)
          else ((nrmBlk (auxMat X)).getD (((ent X 0 1 : Nat) : Int)).toNat (0, 0)).2) = _
    rw [if_neg (by omega), show (((ent X 0 1 : Nat) : Int)).toNat = ent X 0 1 from by omega,
      hgetu]
  have hlenN : lenI (nrmBlk (auxMat X)) = ((ent X 0 1 + X.length : Nat) : Int) := by
    show (((nrmBlk (auxMat X)).length : Nat) : Int) = _
    rw [nrmBlk_length, auxMat_length]
  rw [hgp0N, hgp1N, hlenN, prin_nrmBlk X hblk hlen,
    decide_eq_true (show ((ent X 0 1 : Nat) : Int) ≤ ((ent X 0 1 + X.length : Nat) : Int) - 1
      from by omega)]
  simp only [Bool.and_true, if_true]
  rw [show -((ent X 0 1 : Nat) : Int) + ((ent X 0 1 : Nat) : Int) = 0 from by omega,
    incrFirst_zero]

end

/-! ## §46 `red` IS `nrmM`

    red f (psM X) = nrmM X    for every `LvlOKb X`, with `f` at least `3 * X.length + 2`

which is §36's measured identity, proved.  `redP_nrmM` says the fuel `redFuel` actually passes
is more than enough, so this is a statement about the function the port calls, not about a
convenient variant of it.

The induction is on a bound `n` for `X.length`, and the step dispatches on the number of blocks:

    none          `X = []`                                            redN_nil
    two or more   not principal (§44), and each block is shorter      redN_sum
    exactly one   `blocks X = [X]`, so `BlkG X`, and then

        one column                       red_leaf puts it at (v, v)   redN_one   (§21)
        root level ≥ 1                   prepend a diagonal           redN_head  (§45)
        root level 0, depth > 0          lower every depth            redN_shift (§40)
        root level 0, depth 0            the fold, or the diagonal    redN_block (§44/§45)

Each branch costs at most three fuel and drops the length bound by one, which is where
`3 * n + 2` comes from; the `≥` in the hypothesis is what lets a branch spend a different amount
than its neighbours.

The depth-lowering branch is the only one that does not shorten anything — it lands on
`downMat X`, same length — so it is handled inline rather than through the induction hypothesis:
after one shift the root is at depth 0, which is the fold branch, and that one does recurse into
strictly shorter blocks.  The level-positive branch goes the other way, to a LONGER matrix, and
survives because §45's `runLen_auxMat` makes its branches shorter than `X` (which is why §44's
`redN_fold` carries the bound as a parameter).

`blocks_lvlOKb` and `blocks_lt` are the two facts the several-blocks case needs about a block of
a matrix: it stays in the class, and it is strictly shorter when there is more than one. -/

section
open Trans.Recal


/-! ### 1 列のブロック -/

theorem redN_one (c : Col) (f : Nat) : red (f + 2) (psM [c]) = nrmBlk [c] := by
  show red (f + 2) [(((c.getD 0 0 : Nat) : Int), ((c.getD 1 0 : Nat) : Int))] = _
  rw [red_leaf (c.getD 0 0) f (c.getD 1 0)]
  show _ = (List.range 1).map (fun i =>
    (((ent [c] 0 1 + anc0 [c] i : Nat) : Int), ((ent [c] i 1 : Nat) : Int)))
  rw [show ((List.range 1).map (fun i =>
      (((ent [c] 0 1 + anc0 [c] i : Nat) : Int), ((ent [c] i 1 : Nat) : Int))))
      = [(((ent [c] 0 1 + anc0 [c] 0 : Nat) : Int), ((ent [c] 0 1 : Nat) : Int))] from rfl,
    anc0_zero [c]]
  rfl

theorem redN_block_self (f : Nat) (Z : Matrix) (hblk : BlkG Z) (hlvl : LvlOKb Z = true)
    (h0d : ent Z 0 0 = 0) (h0l : ent Z 0 1 = 0) (hlen : 1 < Z.length)
    (ih : ∀ Y : Matrix, Y.length < Z.length → BlkG Y → LvlOKb Y = true →
            red f (psM Y) = nrmBlk Y) :
    red (f + 1) (psM Z) = nrmBlk Z := by
  refine redN_block f Z Z.length hblk hlvl h0d h0l hlen (fun J hJ => ?_) ih
  have hbe := block_end_le (blocks (Z.drop (runLen Z + 1))) J hJ
  rw [blocks_flatten (Z.drop (runLen Z + 1)).length _ (Nat.le_refl _), List.length_drop] at hbe
  omega

/-! ### ブロック列の長さ -/

theorem off_mono (Bs : List Matrix) : ∀ (b : Nat), b ≤ Bs.length → ∀ a, a ≤ b →
    ((Bs.take a).flatten).length ≤ ((Bs.take b).flatten).length := by
  intro b
  induction b with
  | zero =>
    intro _ a ha
    rw [show a = 0 from by omega]
    omega
  | succ k ih =>
    intro hk a ha
    rcases Nat.lt_or_ge a (k + 1) with h | h
    · have h1 := ih (by omega) a (by omega)
      have h2 := take_succ_flatten_len Bs k (by omega)
      omega
    · rw [show a = k + 1 from by omega]
      omega

theorem blocks_lt (X : Matrix) (h2 : 2 ≤ (blocks X).length) (J : Nat)
    (hJ : J < (blocks X).length) : ((blocks X).getD J []).length < X.length := by
  have hfl := blocks_flatten X.length X (Nat.le_refl _)
  have hbeJ := block_end_le (blocks X) J hJ
  rw [hfl] at hbeJ
  have hlen0 : 0 < ((blocks X).getD 0 []).length :=
    (blocks_blkG X.length X (Nat.le_refl _) _ (getD_mem_list (blocks X) [] 0 (by omega))).1
  have hlen1 : 0 < ((blocks X).getD 1 []).length :=
    (blocks_blkG X.length X (Nat.le_refl _) _ (getD_mem_list (blocks X) [] 1 (by omega))).1
  have h1 : (((blocks X).take 1).flatten).length
      = (((blocks X).take 0).flatten).length + ((blocks X).getD 0 []).length :=
    take_succ_flatten_len (blocks X) 0 (by omega)
  have h00 : (((blocks X).take 0).flatten).length = 0 := rfl
  rcases Nat.eq_zero_or_pos J with rfl | hJpos
  · have hbe1 := block_end_le (blocks X) 1 (by omega)
    rw [hfl] at hbe1
    omega
  · have hmono := off_mono (blocks X) J (by omega) 1 hJpos
    omega

theorem blocks_lvlOKb (X : Matrix) (hlvl : LvlOKb X = true) (J : Nat)
    (hJ : J < (blocks X).length) : LvlOKb ((blocks X).getD J []) = true := by
  have hfl := blocks_flatten X.length X (Nat.le_refl _)
  have hbe := block_end_le (blocks X) J hJ
  rw [hfl] at hbe
  refine lvlOKb_sub X ((blocks X).getD J []) ((((blocks X).take J).flatten).length) hlvl
    (fun i hi => ?_) (fun i hi => ?_) hbe
  · have hh := ent_flatten_block (blocks X) J hJ i 0 hi
    rw [hfl] at hh
    exact hh
  · have hh := ent_flatten_block (blocks X) J hJ i 1 hi
    rw [hfl] at hh
    exact hh

theorem blocks_pos (X : Matrix) (h : 0 < X.length) : 0 < (blocks X).length := by
  cases hxc : X with
  | nil => rw [hxc] at h; exact absurd h (by simp)
  | cons c cs => rw [blocks_cons]; simp

theorem blocks_eq_self (X : Matrix) (h1 : (blocks X).length = 1) : blocks X = [X] := by
  have hfl := blocks_flatten X.length X (Nat.le_refl _)
  cases hbs : blocks X with
  | nil => rw [hbs] at h1; exact absurd h1 (by simp)
  | cons B rest =>
    have hr : rest = [] := by
      have hh : (B :: rest).length = 1 := by rw [← hbs]; exact h1
      have hz : rest.length = 0 := by
        have : rest.length + 1 = 1 := hh
        omega
      exact List.eq_nil_of_length_eq_zero hz
    subst hr
    rw [hbs] at hfl
    have hBX : B = X := by
      have hh : B ++ ([] : List Matrix).flatten = X := hfl
      rw [show ([] : List Matrix).flatten = ([] : Matrix) from rfl, List.append_nil] at hh
      exact hh
    rw [hBX]

/-! ### 全体 -/

/-- **`red` は `nrmM` である。** 燃料は長さの 3 倍と少し。 -/
theorem red_nrmM : ∀ (n : Nat) (X : Matrix), X.length ≤ n → LvlOKb X = true →
    ∀ (f : Nat), 3 * n + 2 ≤ f → red f (psM X) = nrmM X := by
  intro n
  induction n with
  | zero =>
    intro X hlen _ f _
    rw [show X = [] from List.eq_nil_of_length_eq_zero (by omega)]
    exact redN_nil f
  | succ m ih =>
    intro X hlen hlvl f hf
    have ihB : ∀ Y : Matrix, Y.length ≤ m → BlkG Y → LvlOKb Y = true →
        ∀ g, 3 * m + 2 ≤ g → red g (psM Y) = nrmBlk Y := by
      intro Y hY hb hl g hg
      rw [ih Y hY hl g hg, nrmM_single Y hb]
    rcases Nat.eq_zero_or_pos X.length with h0 | hpos
    · rw [show X = [] from List.eq_nil_of_length_eq_zero h0]
      exact redN_nil f
    · rcases Nat.lt_or_ge (blocks X).length 2 with hb1 | hb2
      · -- ブロックは 1 つ
        have hbl1 : (blocks X).length = 1 := by
          have := blocks_pos X hpos
          omega
        have hBX : blocks X = [X] := blocks_eq_self X hbl1
        have hblk : BlkG X :=
          blocks_blkG X.length X (Nat.le_refl _) X (by rw [hBX]; exact List.mem_singleton.mpr rfl)
        rw [nrmM_single X hblk]
        rcases Nat.lt_or_ge X.length 2 with hshort | hlong
        · obtain ⟨c, hc⟩ : ∃ c, X = [c] := by
            cases hxc : X with
            | nil => rw [hxc] at hpos; exact absurd hpos (by simp)
            | cons c cs =>
              refine ⟨c, ?_⟩
              have : cs.length = 0 := by
                rw [hxc] at hshort
                have : cs.length + 1 < 2 := hshort
                omega
              rw [List.eq_nil_of_length_eq_zero this]
          obtain ⟨f2, rfl⟩ : ∃ f2, f = f2 + 2 := ⟨f - 2, by omega⟩
          rw [hc]
          exact redN_one c f2
        · rcases Nat.eq_zero_or_pos (ent X 0 1) with hu0 | hu1
          · rcases Nat.eq_zero_or_pos (ent X 0 0) with hd0 | hd1
            · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
              exact redN_block_self g X hblk hlvl hd0 hu0 hlong
                (fun Y hY hb hl => ihB Y (by omega) hb hl g (by omega))
            · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 + 1 := ⟨f - 2, by omega⟩
              rw [redN_shift (g + 1) X hblk hlong hu0 hd1, ← nrmBlk_downMat X hblk]
              exact redN_block_self g (downMat X)
                (blkG_downMat X hblk) (lvlOKb_downMat X hblk hlvl)
                (by rw [ent_downMat0 X 0 hblk.1]; omega)
                (by rw [ent_downMat1 X 0 hblk.1]; exact hu0)
                (by rw [downMat_length]; exact hlong)
                (fun Y hY hb hl =>
                  ihB Y (by rw [downMat_length] at hY; omega) hb hl g (by omega))
          · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 + 1 := ⟨f - 2, by omega⟩
            exact redN_head g X hblk hlvl hu1 hlong
              (fun Y hY hb hl => ihB Y (by omega) hb hl g (by omega))
      · -- ブロックが 2 つ以上
        have hlen0 : 0 < ((blocks X).getD 0 []).length :=
          (blocks_blkG X.length X (Nat.le_refl _) _
            (getD_mem_list (blocks X) [] 0 (by omega))).1
        have hX2 : 1 < X.length := by
          have := blocks_lt X hb2 0 (by omega)
          omega
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        refine redN_sum g X ?_ (not_prin_of_blocks X hb2) (fun Bk hBk => ?_)
        · show ((psM X).length == 1 && _) = false
          rw [show ((psM X).length == 1) = false from by
            rw [psM_len]; exact decide_eq_false (by omega)]
          rfl
        · obtain ⟨J, hJ, hJeq⟩ := List.mem_iff_getElem.mp hBk
          have hgd : (blocks X).getD J [] = Bk := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ, hJeq]
            rfl
          rw [← hgd]
          exact ihB ((blocks X).getD J [])
            (by have := blocks_lt X hb2 J hJ; omega)
            (blocks_blkG X.length X (Nat.le_refl _) _ (getD_mem_list (blocks X) [] J hJ))
            (blocks_lvlOKb X hlvl J hJ) g (by omega)

/-- **`redP` の形。** 実際の燃料 `redFuel` は足りている。 -/
theorem redP_nrmM (X : Matrix) (hlvl : LvlOKb X = true) : redP (psM X) = nrmM X := by
  show red (redFuel (psM X)) (psM X) = _
  refine red_nrmM X.length X (Nat.le_refl _) hlvl (redFuel (psM X)) ?_
  show 3 * X.length + 2 ≤ 40 + 4 * ((psM X).length + maxE (psM X))
  rw [psM_len]
  omega

-- 測ったところと合う (§37 の母集団)。
#guard freePopL.all fun M => redP (psM M) == nrmM M

end

/-! ## §47 THE NORMAL-FORM INDICES ARE REDUCED

§19 measured that `nfB` and `isReducedP` agree on 220 / 5101 / 16332 enumerated indices.  With
§46 in hand the forward half is a theorem, and it is the half the port needs: `runAux`'s first
branch reduces its argument, so running it on `matB t 0` requires knowing the reduction is the
identity there.

    isReducedP_iff   for `LvlOKb X`, `isReducedP (psM X) = (nrmM X == psM X)`   [§46]
    isReducedP_matB  `nfB t → isReducedP (psM (matB t 0)) = true`

The bridge is that `matB` builds depth = TREE DEPTH by construction, and `nrmM` puts every
column at `block root level + tree depth`.  So the two agree exactly when every block root has
level 0 — which under `nfB` is every top-level node, and `nfB` says their level is 0.

    anc0_eq_depth   tree depth = depth, when depth steps by at most one and the root is at 0
    lvlOKb_of_nfm   §31's `NFM` (the tree condition) implies §37's `LvlOKb` (the class)
    nrmBlk_eq_psM   so a block whose root sits at depth 0 and level 0 is already its own answer
    matB_lvl_top    and under `nfLe m`, every column at the top depth has level at most `m`

`parent_depth_succ` is the small fact underneath: the row-0 parent's depth is exactly one less,
because it is the LAST shallower column and the depths cannot jump.  That is also what turns
`LMin`/`LvlOK` into `parent`/`LvlOKb`, so §31 and §37 are finally the same condition.

WHAT IS NOT CLAIMED.  The converse — a non-normal-form index is not reduced — is still only
measured (§19's guards).  Proving it needs the transfer in the other direction (matrix condition
back to tree condition), and for a non-`LvlOKb` matrix §46 says nothing at all. -/

section
open Trans.Recal


/-! ### 親と左極小 -/

theorem lmin_of_parent (M : Matrix) (i p : Nat) (hp : parent M 0 i = some p) : LMin M p i := by
  obtain ⟨hpm, hpmax⟩ := List.max?_eq_some_iff.mp hp
  have hpi : p < i := List.mem_range.mp (List.mem_filter.mp hpm).1
  have hplt : ent M p 0 < ent M i 0 := of_decide_eq_true (List.mem_filter.mp hpm).2
  refine ⟨hpi, fun q hq1 hq2 => ?_⟩
  rcases Nat.lt_or_ge q i with hqi | hqi
  · rcases Nat.lt_or_ge (ent M q 0) (ent M i 0) with hc | hc
    · exfalso
      have := hpmax q (List.mem_filter.mpr ⟨List.mem_range.mpr hqi, decide_eq_true hc⟩)
      omega
    · omega
  · rw [show q = i from by omega]
    exact hplt

/-- **深さが 1 段ずつしか増えないなら、親の深さはちょうど 1 つ下。** -/
theorem parent_depth_succ (X : Matrix) (hstep : StepOK X) (i p : Nat)
    (hp : parent X 0 i = some p) : ent X p 0 + 1 = ent X i 0 := by
  obtain ⟨hpm, hpmax⟩ := List.max?_eq_some_iff.mp hp
  have hpi : p < i := List.mem_range.mp (List.mem_filter.mp hpm).1
  have hplt : ent X p 0 < ent X i 0 := of_decide_eq_true (List.mem_filter.mp hpm).2
  have hs := hstep p
  rcases Nat.eq_or_lt_of_le (show p + 1 ≤ i from by omega) with heq | hlt
  · subst heq; omega
  · have hnc : ¬(ent X (p + 1) 0 < ent X i 0) := by
      intro hc
      have := hpmax (p + 1) (List.mem_filter.mpr
        ⟨List.mem_range.mpr (by omega), decide_eq_true hc⟩)
      omega
    omega

/-- **木の深さ = 深さ。** 深さが 1 段ずつしか増えず、根が深さ 0 のとき。 -/
theorem anc0_eq_depth (X : Matrix) (hstep : StepOK X) (h0 : ent X 0 0 = 0) :
    ∀ (n i : Nat), i ≤ n → i < X.length → anc0 X i = ent X i 0 := by
  intro n
  induction n with
  | zero =>
    intro i hi _
    rw [show i = 0 from by omega, anc0_zero X, h0]
  | succ g ih =>
    intro i hi hlen
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [anc0_zero X, h0]
    · cases hp : parent X 0 i with
      | none =>
        have hnil : ((List.range i).filter (fun q => decide (ent X q 0 < ent X i 0))) = [] :=
          List.max?_eq_none_iff.mp hp
        have h0not : ¬(ent X 0 0 < ent X i 0) := by
          intro hc
          have hmem : (0 : Nat)
              ∈ ((List.range i).filter (fun q => decide (ent X q 0 < ent X i 0))) :=
            List.mem_filter.mpr ⟨List.mem_range.mpr hipos, decide_eq_true hc⟩
          rw [hnil] at hmem
          exact absurd hmem (by simp)
        have hz : anc0 X i = 0 := by
          show (iterParent (parent X 0) X.length i).length = 0
          cases hn : X.length with
          | zero => rfl
          | succ _ => rw [iterParent_nil hp]; rfl
        omega
      | some p =>
        have hpi := parent0_lt X i p hp
        rw [anc0_succ X i p hlen hp, ih p (by omega) (by omega),
          parent_depth_succ X hstep i p hp]

/-- **`NFM` なら `LvlOKb`。** §31 の木の条件と §37 の類は同じもの。 -/
theorem lvlOKb_of_nfm (X : Matrix) (h : NFM X) : LvlOKb X = true := by
  show ((List.range X.length).all _) = true
  refine List.all_eq_true.mpr (fun i hi => ?_)
  cases hp : parent X 0 i with
  | none => rfl
  | some p =>
    show decide (ent X i 1 ≤ ent X p 1 + 1) = true
    exact decide_eq_true (h.2 p i (lmin_of_parent X i p hp)
      (parent_depth_succ X h.1 i p hp))

/-! ### 位置で書いた `psM` -/

theorem psM_eq_map_range (X : Matrix) :
    psM X = (List.range X.length).map
      (fun i => (((ent X i 0 : Nat) : Int), ((ent X i 1 : Nat) : Int))) := by
  have h1 : (psM X).take (psM X).length = psM X := List.take_of_length_le (Nat.le_refl _)
  rw [← h1, take_eq_map_range ((0 : Int), (0 : Int)) (psM X).length (psM X) (Nat.le_refl _),
    psM_len]
  exact List.map_congr_left (fun i _ => getD_psM X i)

/-- **深さがもともと木の深さで根の段が 0 なら、答えは入力そのもの。** -/
theorem nrmBlk_eq_psM (X : Matrix) (hstep : StepOK X) (h0d : ent X 0 0 = 0)
    (h0l : ent X 0 1 = 0) : nrmBlk X = psM X := by
  rw [psM_eq_map_range X]
  show (List.range X.length).map _ = _
  refine List.map_congr_left (fun i hi => ?_)
  have hi' : i < X.length := List.mem_range.mp hi
  show (((ent X 0 1 + anc0 X i : Nat) : Int), ((ent X i 1 : Nat) : Int)) = _
  rw [h0l, anc0_eq_depth X hstep h0d X.length i (by omega) hi',
    show 0 + ent X i 0 = ent X i 0 from by omega]

/-! ### `matB` の最上位の段 -/

theorem ent_cons0 (c : Col) (cs : Matrix) (y : Nat) : ent (c :: cs) 0 y = c.getD y 0 := rfl

theorem ent_cons (c : Col) (cs : Matrix) (j y : Nat) :
    ent (c :: cs) (j + 1) y = ent cs j y := rfl

/-- **最上位 (深さ `d`) の列の段は `m` 以下。** -/
theorem matB_lvl_top : ∀ (t : B) (m d : Nat), nfLe m t = true →
    ∀ j, j < (matB t d).length → ent (matB t d) j 0 = d → ent (matB t d) j 1 ≤ m := by
  intro t
  induction t with
  | nil => intro m d _ j hj _; exact absurd hj (by simp [matB])
  | nd v r a ihr _ =>
    intro m d hnf j hj hd
    obtain ⟨hv, hr, _⟩ := (nfLe_nd_iff m v r a).mp hnf
    have hM : matB (.nd v r a) d = matB r d ++ ([d, v] :: matB a (d + 1)) := rfl
    rcases Nat.lt_or_ge j (matB r d).length with hlo | hhi
    · rw [hM, ent_append_left _ _ j 1 hlo]
      refine ihr m d hr j hlo ?_
      rw [hM, ent_append_left _ _ j 0 hlo] at hd
      exact hd
    · obtain ⟨k, hk⟩ : ∃ k, j = (matB r d).length + k := ⟨j - (matB r d).length, by omega⟩
      subst hk
      rw [hM, ent_append _ _ _ 1 (by omega),
        show (matB r d).length + k - (matB r d).length = k from by omega]
      rw [hM, ent_append _ _ _ 0 (by omega),
        show (matB r d).length + k - (matB r d).length = k from by omega] at hd
      cases k with
      | zero => rw [ent_cons0]; exact hv
      | succ q =>
        exfalso
        rw [ent_cons] at hd
        have hqlen : q < (matB a (d + 1)).length := by
          rw [hM, List.length_append] at hj
          have : ([d, v] :: matB a (d + 1)).length = (matB a (d + 1)).length + 1 := rfl
          omega
        have hlb := matB_col_lb a (d + 1) _ (getD_mem (matB a (d + 1)) [] q hqlen)
        have : ent (matB a (d + 1)) q 0 = ((matB a (d + 1)).getD q []).getD 0 0 := rfl
        omega

/-! ### 標準形の添字は既約 -/

/-- **`LvlOKb` なら既約かどうかは `nrmM` と等しいかどうか。** -/
theorem isReducedP_iff (X : Matrix) (h : LvlOKb X = true) :
    isReducedP (psM X) = (nrmM X == psM X) := by
  show (redP (psM X) == psM X) = _
  rw [redP_nrmM X h]

theorem nrmM_matB (t : B) (h : nfB t = true) : nrmM (matB t 0) = psM (matB t 0) := by
  rcases (show t = .nil ∨ t ≠ .nil from by
      cases t with
      | nil => exact Or.inl rfl
      | nd _ _ _ => exact Or.inr (by intro hc; exact B.noConfusion hc)) with rfl | hne
  · show nrmM ([] : Matrix) = _
    rw [nrmM_nil]
    rfl
  · have hnfm : NFM (matB t 0) := nfm_matB t 0 0 h
    have hfl := blocks_flatten (matB t 0).length (matB t 0) (Nat.le_refl _)
    have hkey : ∀ Bk ∈ blocks (matB t 0), nrmBlk Bk = psM Bk := by
      intro Bk hBk
      obtain ⟨J, hJ, hJeq⟩ := List.mem_iff_getElem.mp hBk
      have hgd : (blocks (matB t 0)).getD J [] = Bk := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ, hJeq]
        rfl
      have hblkG : BlkG Bk := blocks_blkG (matB t 0).length (matB t 0) (Nat.le_refl _) Bk hBk
      have hnfmBk : NFM Bk :=
        nfm_blocks (matB t 0).length (matB t 0) (Nat.le_refl _) hnfm Bk hBk
      have hroot0 : ent Bk 0 0 = 0 := by
        have hle := blocks_root_le (matB t 0).length (matB t 0) (Nat.le_refl _) J hJ
        rw [hgd, matB_head0 t 0 hne] at hle
        omega
      have hbe := block_end_le (blocks (matB t 0)) J hJ
      rw [hfl, hgd] at hbe
      have hpos0 : ent (matB t 0)
          ((((blocks (matB t 0)).take J).flatten).length) 0 = ent Bk 0 0 := by
        have hh := ent_flatten_block (blocks (matB t 0)) J hJ 0 0 (by rw [hgd]; exact hblkG.1)
        rw [hfl, hgd, show (((blocks (matB t 0)).take J).flatten).length + 0
          = (((blocks (matB t 0)).take J).flatten).length from by omega] at hh
        exact hh
      have hpos1 : ent (matB t 0)
          ((((blocks (matB t 0)).take J).flatten).length) 1 = ent Bk 0 1 := by
        have hh := ent_flatten_block (blocks (matB t 0)) J hJ 0 1 (by rw [hgd]; exact hblkG.1)
        rw [hfl, hgd, show (((blocks (matB t 0)).take J).flatten).length + 0
          = (((blocks (matB t 0)).take J).flatten).length from by omega] at hh
        exact hh
      have hroot1 : ent Bk 0 1 = 0 := by
        have hlt := matB_lvl_top t 0 0 h ((((blocks (matB t 0)).take J).flatten).length)
          (by have := hblkG.1; omega) (by rw [hpos0, hroot0])
        omega
      exact nrmBlk_eq_psM Bk hnfmBk.1 hroot0 hroot1
    show ((blocks (matB t 0)).map nrmBlk).flatten = _
    rw [List.map_congr_left hkey, ← psM_flatten, hfl]

/-- **標準形の添字の行列は既約。** §19 で測っていた等式の片側。 -/
theorem isReducedP_matB (t : B) (h : nfB t = true) :
    isReducedP (psM (matB t 0)) = true := by
  show (redP (psM (matB t 0)) == psM (matB t 0)) = true
  rw [redP_nrmM (matB t 0) (lvlOKb_of_nfm (matB t 0) (nfm_matB t 0 0 h)), nrmM_matB t h]
  exact beq_self_eq_true _

end

/-! ## §48 A CLOSED FORM FOR `Trans` ON THE NORMAL-FORM INDICES

`red` is settled (§46) and the normal-form indices are reduced (§47), so `runAux` on
`matB t 0` never takes its reduction branch and the question becomes: what does it return?
This section answers it as a recursion on `B` — no matrices, no memo table.

    bVal t = transPort (psM (matB t 0))

MEASURED on every normal-form index of the enumerations: 670 (levels < 3, ≤ 6 nodes) and 697
(levels < 4), frozen as guards below; during development also 39446 (levels < 3, ≤ 8 nodes),
5443 (levels < 4, ≤ 7) and 698 (levels < 5, ≤ 6).  Zero mismatches.

THE THREE RULES.  Write `w` for a node's level and read the children left to right.

  * A node's ARGUMENT (`bArg`) is its children's contributions in order.  `bVal` reads the
    top-level nodes as a sum: the FIRST `(0,0)` contributes 0 and every later one contributes 1
    — that is the `1 +` convention of `oR`, and it is `red`'s `ppair` branch.

  * A child of level `u ≤ w`, or any child that is not the first, contributes `psi_u(its
    argument)` — the obvious thing.

  * A child of level `u > w` that IS first and whose own first child is higher still contributes
    something else: `bFold`, which keeps the sum built so far AND an argument being accumulated,
    emits high grandchildren at the outer level, and closes a whole RUN of low ones into a single
    `psi_u(...)` whose argument is the outer sum at the start of the run plus that run.

WHY AN ACCUMULATOR.  The contribution of a subtree is not a function of the subtree.  The
guards at the end of the section exhibit the same shape three times:

    (1,1)(2,2)                    on its own          psi_1(Omega_2)
    (0,0)(1,1)(2,2)               as the first child  Omega_2          — the psi_1 is gone
    (0,0)(1,0)(1,1)(2,2)          with a sibling      psi_1(Omega_2)   — it is back

That is exactly what `replMark` implements in the reference: a value is substituted INTO the
previous answer, so where a subtree sits changes what it contributes.  Any specification of the
port has to carry that context, and `bFold`'s pair is the smallest form of it that reproduces
the reference — the two remaining guards pin the run behaviour, which is what distinguishes it
from a plain left fold.

WHAT IS NOT CLAIMED.  Everything here is measured.  The proof has to go through `runAux`'s memo
table, the way `Rows/G3`, `G4` and `G11` did for their ladders — `bVal` is what their `Val` was
per family, now written once for the whole region. -/

section
open Trans.Recal
open Trans.Dict (BT)


/-- 溜めている「低い子」の分を `psi_w` で閉じる。 -/
def bClose (w : Nat) (st : BT × Option BT) : BT :=
  match st.2 with
  | none => st.1
  | some a => bplus st.1 (.D w a)

mutual
/-- **段 `w` の節の引数。** 子の寄与をそのまま左から並べたもの。 -/
def bArg : Nat → B → BT
  | _, .nil => .zero
  | w, .nd u r c =>
      bplus (bArg w r)
        (if c == .nil then .D u .zero
         else if u ≤ w || !(r == .nil) || headLvl c ≤ u then .D u (bArg u c)
         else bClose u (bFold u c))
/-- **段 `w` の節の寄与を作る畳み込み。** 第 1 成分は閉じた分、第 2 成分は
    今の「低い子」の連なりのために溜めている引数。 -/
def bFold : Nat → B → BT × Option BT
  | _, .nil => (.zero, none)
  | w, .nd u r c =>
      let st := bFold w r
      let K : BT :=
        if c == .nil then .D u .zero
        else if u ≤ w || !(r == .nil) || headLvl c ≤ u then .D u (bArg u c)
        else bClose u (bFold u c)
      if w < u then (bplus (bClose w st) K, none)
      else
        match st.2 with
        | none => (st.1, some (bplus st.1 K))
        | some a => (st.1, some (bplus a K))
end

/-- **添字の値。** 最上位の節を左から足す — 先頭の `(0,0)` だけが 0。 -/
def bVal : B → BT
  | .nil => .zero
  | .nd w r c =>
      bplus (bVal r) (if r == .nil && w == 0 && c == .nil then .zero else .D w (bArg w c))

/-- 標準形の添字の母集団。 -/
def popNFB (L n : Nat) : List B :=
  ((List.range n).flatMap (enumNodes L)).filter fun t => nfB t && t != .nil

#guard (popNFB 3 6).length == 670
#guard (popNFB 4 6).length == 697
-- **測定: 移植した `Trans` の値はこの閉じた形。**
#guard (popNFB 3 6).all fun t => transPort (psM (matB t 0)) == bVal t
#guard (popNFB 4 6).all fun t => transPort (psM (matB t 0)) == bVal t

/-! ### 蓄積器が要る理由 (測定) -/

-- 同じ部分木が、左に兄弟があるかどうかで**別の寄与**をする。
#guard Test.showRaw (transPort (psM [[1, 1], [2, 2]])) == "D_1 D_2 0"
#guard Test.showRaw (transPort (psM [[0, 0], [1, 1], [2, 2]])) == "D_0 D_2 0"
#guard Test.showRaw (transPort (psM [[0, 0], [1, 0], [1, 1], [2, 2]]))
  == "D_0 (D_0 0,D_1 D_2 0)"
-- 低い子の**連なり**は 1 つの `psi_w` に閉じ、高い子が来ると切れる。
#guard Test.showRaw (transPort (psM [[0, 0], [1, 1], [2, 2], [2, 0], [2, 0]]))
  == "D_0 (D_2 0,D_1 (D_2 0,D_0 0,D_0 0))"
#guard Test.showRaw (transPort (psM [[0, 0], [1, 1], [2, 2], [2, 0], [2, 2], [2, 0]]))
  == "D_0 (D_2 0,D_1 (D_2 0,D_0 0),D_2 0,D_1 (D_2 0,D_1 (D_2 0,D_0 0),D_2 0,D_0 0))"

end

/-! ## §49 THE MARKS

§48 gives `Trans`.  `runAux` also computes `Mark m`, and a proof has to say what those are too —
that is what `Rows/G11`'s `markV1` / `markV2` were, per rung.  This section says it once.

    bMark t m = Mark m (psM (matB t 0))      whenever `markOKB t m`

MEASURED on the same enumerations as §48 (670 and 697 indices, every position of each), and
during development also at seven nodes.  Zero mismatches.

WHAT `Mark m` IS.  The CONTRIBUTION of the node at preorder position `m` — the very `K` that
§48's `bArg` inserts into its parent's argument, collapse rule and all.  Not its value: for a
node that §48 collapses (first child, higher than its parent, own first child higher still) the
mark is the collapsed form, which is why `markIn` repeats §48's three-way test instead of just
returning `psi_u(...)`.

WHERE IT IS DEFINED.  Not everywhere.  `Mark m` returns a fallback (`psi` of the LAST column's
level) when the mark cannot be found, so a specification has to name the positions where it
means something:

    m is on the last column's row-0 ancestor chain  — `lastSpine`, read off the tree as
                                                      "last top-level node, then its last
                                                      child, and so on"
    and the contribution is a single `psi` term     — a sum means "not findable"

`markOKB` is the conjunction, and the last guard checks the containment that makes it usable as
an `Allowed` predicate: every mark the algorithm actually requests when running on `matB t 0`
lies on that chain.

WHAT IS NOT CLAIMED.  Measured, like §48.  Together the two give the `Val` of a `Good`/`Sound`
argument over `runAux`'s memo table — `Val t none = bVal t`, `Val t (some m) = bMark t m` — for
the whole region rather than one family at a time. -/

section
open Trans.Recal
open Trans.Dict (BT)


/-- 添字の節の個数 (= `matB t d` の列数)。 -/
def sizeB : B → Nat
  | .nil => 0
  | .nd _ r a => sizeB r + 1 + sizeB a

/-- 前順で `m` 番目の節の**寄与**。`w` は親の段。 -/
def markIn (w : Nat) : B → Nat → Option BT
  | .nil, _ => none
  | .nd u r c, m =>
      let lr := sizeB r
      if m < lr then markIn w r m
      else if m == lr then
        some (if c == .nil then .D u .zero
              else if u ≤ w || !(r == .nil) || headLvl c ≤ u then .D u (bArg u c)
              else bClose u (bFold u c))
      else markIn u c (m - lr - 1)

/-- **`Mark m` の値。** 最上位の `(0,0)` だけが 0。 -/
def bMark (t : B) (m : Nat) : BT :=
  match t with
  | .nd 0 .nil .nil => .zero
  | _ => (markIn 0 t m).getD .zero

/-- 最後の列の行 0 の祖先鎖 (自分を含む) の前順添字。 -/
def lastSpine : B → List Nat
  | .nil => []
  | .nd _ r c =>
      let lr := sizeB r
      lr :: (lastSpine c).map (fun i => lr + 1 + i)

/-- **`Mark m` が意味を持つ添字。** 最後の列の祖先で、寄与が 1 つの `D` になるもの。 -/
def markOKB (t : B) (m : Nat) : Bool :=
  m ∈ lastSpine t && (match bMark t m with | .D _ _ => true | _ => false)

/-! ### 測定 -/

def markRun (M : PS) (m : Int) : BT := (Trans.Recal.runAux (transFuel M) M (some m)).run' []
def memoKeys (M : PS) : List ((PS × Option Int) × BT) :=
  ((Trans.Recal.runAux (transFuel M) M none).run []).2

def popNFB' (L n : Nat) : List B :=
  ((List.range n).flatMap (enumNodes L)).filter fun t => nfB t && t != .nil

#guard (popNFB' 3 6).length == 670
-- 節の個数は列の数。
#guard (popNFB' 3 6).all fun t => sizeB t == (matB t 0).length
-- 祖先鎖の読み替えは行列の側と合う。
#guard (popNFB' 3 6).all fun t =>
  let P := psM (matB t 0)
  (List.range (sizeB t)).all fun m =>
    (m ∈ lastSpine t) == (Int.ofNat m == lenI P - 1 || isAnc P 0 (lenI P - 1) (Int.ofNat m))
-- **測定: 意味を持つ添字では `Mark m` はこの閉じた形。**
#guard (popNFB' 3 6).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m) || markRun (psM (matB t 0)) (Int.ofNat m) == bMark t m
#guard (popNFB' 4 6).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m) || markRun (psM (matB t 0)) (Int.ofNat m) == bMark t m
-- **測定: 走らせたときに実際に要求される `Mark` はすべて祖先鎖の上。**
#guard (popNFB' 3 6).all fun t =>
  (memoKeys (psM (matB t 0))).all fun p =>
    match p.1.2 with
    | none => true
    | some m => m == lenI p.1.1 - 1 || isAnc p.1.1 0 (lenI p.1.1 - 1) m

end

/-! ## §50 THE MEMO TABLE

§48 and §49 say what `runAux` returns; proving it means running the same argument `Rows/G3`,
`G4` and `G11` ran for their ladders — an induction that carries the memo table and its
invariant.  This section builds that scaffolding once, for indices instead of rungs.

    bValReq t none      = bVal t          (§48)
    bValReq t (some m)  = bMark t m       (§49)
    AllowedB t req      the requests a proof is responsible for
    GoodB p             "if this entry's key is an index of ours, its value is `bValReq`"
    SoundB tbl          every entry is `GoodB`

The one thing that is not bookkeeping is `goodB_mk`: an entry pushed for index `s` has to be
`GoodB`, which means its value must be right for EVERY index whose matrix is that key — so the
encoding has to be injective, and `matB_inj` proves it is.  The reason is local: in
`matB (nd v r a) d = matB r d ++ [d, v] :: matB a (d+1)` every column after the node is deeper
than `d` (`matB_deep_after`), so the node's position is the LAST column of depth `d` and the
three pieces can be read back off the list.  `psM_inj_matB` carries that through `psM`, which
loses nothing because `matB`'s columns have exactly two rows.

`runHit` is the memo-hit step of `runAux`, proved here rather than imported: `Rows/Selected.lean`
has the same lemma, but it sits above this file. -/

section
open Trans.Recal
open Trans.Dict (BT)


/-! ### `matB` は単射 -/

theorem matB_len_nd (v : Nat) (r a : B) (d : Nat) :
    (matB (.nd v r a) d).length = (matB r d).length + 1 + (matB a (d + 1)).length := by
  show (matB r d ++ ([d, v] :: matB a (d + 1))).length = _
  rw [List.length_append, List.length_cons]
  omega

theorem matB_eq_nil_iff : ∀ (t : B) (d : Nat), matB t d = [] ↔ t = .nil
  | .nil, _ => ⟨fun _ => rfl, fun _ => rfl⟩
  | .nd v r a, d => by
      constructor
      · intro h
        exfalso
        have hlen : (matB (.nd v r a) d).length = 0 := by rw [h]; rfl
        have := matB_len_nd v r a d
        omega
      · intro h
        exact absurd h (by intro hc; exact B.noConfusion hc)

theorem matB_root_ent (v : Nat) (r a : B) (d y : Nat) :
    ent (matB (.nd v r a) d) (matB r d).length y = ([d, v] : Col).getD y 0 := by
  show ent (matB r d ++ ([d, v] :: matB a (d + 1))) (matB r d).length y = _
  rw [ent_append _ _ _ y (Nat.le_refl _),
    show (matB r d).length - (matB r d).length = 0 from by omega]
  rfl

theorem matB_deep_after (v : Nat) (r a : B) (d i : Nat)
    (h1 : (matB r d).length < i) (h2 : i < (matB (.nd v r a) d).length) :
    d < ent (matB (.nd v r a) d) i 0 := by
  obtain ⟨k, hk⟩ : ∃ k, i = (matB r d).length + 1 + k := ⟨i - (matB r d).length - 1, by omega⟩
  subst hk
  have hklen : k < (matB a (d + 1)).length := by
    rw [matB_len_nd] at h2
    omega
  have hstep : ent (matB (.nd v r a) d) ((matB r d).length + 1 + k) 0
      = ent (matB a (d + 1)) k 0 := by
    show ent (matB r d ++ ([d, v] :: matB a (d + 1))) ((matB r d).length + 1 + k) 0 = _
    rw [ent_append _ _ _ 0 (by omega),
      show (matB r d).length + 1 + k - (matB r d).length = k + 1 from by omega]
    rfl
  rw [hstep]
  have hlb := matB_col_lb a (d + 1) _ (getD_mem (matB a (d + 1)) [] k hklen)
  have : ent (matB a (d + 1)) k 0 = ((matB a (d + 1)).getD k []).getD 0 0 := rfl
  omega

/-- **添字は行列から読み取れる。** -/
theorem matB_inj : ∀ (s s' : B) (d : Nat), matB s d = matB s' d → s = s' := by
  intro s
  induction s with
  | nil =>
    intro s' d h
    exact ((matB_eq_nil_iff s' d).mp h.symm).symm
  | nd v r a ihr iha =>
    intro s' d h
    cases s' with
    | nil =>
      exact absurd ((matB_eq_nil_iff _ d).mp h) (by intro hc; exact B.noConfusion hc)
    | nd v' r' a' =>
      have hlen : (matB r d).length = (matB r' d).length := by
        rcases Nat.lt_trichotomy (matB r d).length (matB r' d).length with hlt | heq | hgt
        · exfalso
          have hb : (matB r' d).length < (matB (.nd v r a) d).length := by
            rw [h, matB_len_nd]
            omega
          have h1 := matB_deep_after v r a d (matB r' d).length hlt hb
          have h2 : ent (matB (.nd v' r' a') d) (matB r' d).length 0 = d :=
            matB_root_ent v' r' a' d 0
          rw [h] at h1
          omega
        · exact heq
        · exfalso
          have hb : (matB r d).length < (matB (.nd v' r' a') d).length := by
            rw [← h, matB_len_nd]
            omega
          have h1 := matB_deep_after v' r' a' d (matB r d).length hgt hb
          have h2 : ent (matB (.nd v r a) d) (matB r d).length 0 = d :=
            matB_root_ent v r a d 0
          rw [← h] at h1
          omega
      have hM : matB r d ++ ([d, v] :: matB a (d + 1))
          = matB r' d ++ ([d, v'] :: matB a' (d + 1)) := h
      obtain ⟨hr, htail⟩ := List.append_inj hM hlen
      have hv : v = v' := by
        have := List.head_eq_of_cons_eq htail
        have hh : ([d, v] : Col) = [d, v'] := this
        have := congrArg (fun c => List.getD c 1 0) hh
        exact this
      have ha : matB a (d + 1) = matB a' (d + 1) := List.tail_eq_of_cons_eq htail
      rw [ihr r' d hr, iha a' (d + 1) ha, hv]

theorem col_two (c : Col) (h : c.length = 2) : c = [c.getD 0 0, c.getD 1 0] := by
  match c, h with
  | [_, _], _ => rfl

theorem congrArg₂' {x y x' y' : Nat} (h1 : x = x') (h2 : y = y') :
    ([x, y] : Col) = [x', y'] := by rw [h1, h2]

theorem psM_inj_matB (s s' : B) (h : psM (matB s 0) = psM (matB s' 0)) : s = s' := by
  refine matB_inj s s' 0 ?_
  have hlen : (matB s 0).length = (matB s' 0).length := by
    have := congrArg List.length h
    rw [psM_len, psM_len] at this
    exact this
  refine List.ext_getElem hlen (fun i h1 h2 => ?_)
  have hi : ((psM (matB s 0)).getD i (0, 0)) = ((psM (matB s' 0)).getD i (0, 0)) := by
    rw [h]
  rw [getD_psM, getD_psM] at hi
  have e0 : ent (matB s 0) i 0 = ent (matB s' 0) i 0 := by
    have := congrArg Prod.fst hi
    omega
  have e1 : ent (matB s 0) i 1 = ent (matB s' 0) i 1 := by
    have := congrArg Prod.snd hi
    omega
  have hc0 := matB_col_len s 0 _ (getD_mem (matB s 0) [] i h1)
  have hc1 := matB_col_len s' 0 _ (getD_mem (matB s' 0) [] i h2)
  have g0 : (matB s 0).getD i [] = (matB s' 0).getD i [] := by
    rw [col_two _ hc0, col_two _ hc1]
    exact congrArg₂' e0 e1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at g0
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at g0
  exact g0

/-! ### memo 表の不変量 -/

/-- 領域の `Val` — §48 と §49 を 1 つにしたもの。 -/
def bValReq (t : B) : Option Int → BT
  | none => bVal t
  | some m => bMark t m.toNat

/-- 許される要求。 -/
def AllowedB (t : B) (req : Option Int) : Prop :=
  req = none ∨ ∃ m : Nat, req = some ((m : Nat) : Int) ∧ markOKB t m = true

/-- memo 表の 1 項が正しいこと。 -/
def GoodB (p : (Trans.Recal.PS × Option Int) × BT) : Prop :=
  ∀ (s : B) (req : Option Int), nfB s = true → p.1 = (psM (matB s 0), req) →
    AllowedB s req → p.2 = bValReq s req

def SoundB (tbl : Trans.Recal.Memo) : Prop := ∀ p ∈ tbl, GoodB p

theorem SoundB_nil : SoundB [] := by
  intro p hp
  exact absurd hp (by simp)

theorem SoundB_cons {tbl : Trans.Recal.Memo} (hs : SoundB tbl)
    {p : (Trans.Recal.PS × Option Int) × BT} (hp : GoodB p) : SoundB (p :: tbl) := by
  intro q hq
  rcases List.mem_cons.mp hq with h | h
  · subst h; exact hp
  · exact hs q h

theorem goodB_of_find {tbl : Trans.Recal.Memo} (hs : SoundB tbl)
    {key : Trans.Recal.PS × Option Int} {p : (Trans.Recal.PS × Option Int) × BT}
    (h : tbl.find? (fun z => z.1 == key) = some p) : GoodB p ∧ p.1 = key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h), ?_⟩
  have hb : p.1 == key := List.find?_some (p := fun z => z.1 == key) (a := p) h
  exact eq_of_beq hb

/-- **新しく積む項はいつでも正しい。** `matB` が単射なので他の添字とぶつからない。 -/
theorem goodB_mk (s : B) (req : Option Int) :
    GoodB ((psM (matB s 0), req), bValReq s req) := by
  intro s' req' _ heq _
  have h1 : psM (matB s 0) = psM (matB s' 0) := congrArg Prod.fst heq
  have h2 : req = req' := congrArg Prod.snd heq
  rw [psM_inj_matB s s' h1, h2]

/-- memo に当たったときは表をそのままに値を返す。 -/
theorem runHit (f : Nat) (M : Trans.Recal.PS) (req : Option Int) (tbl : Trans.Recal.Memo)
    (p : (Trans.Recal.PS × Option Int) × BT)
    (h : tbl.find? (fun q => q.1 == (M, req)) = some p) :
    (Trans.Recal.runAux (f + 1) M req).run tbl = (p.2, tbl) := by
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
    get, getThe, MonadStateOf.get, h]

end

/-! ## §51 WHAT `runAux` RECURSES INTO, AS INDICES

The induction of §50 has to name `runAux`'s recursive arguments on the index side.  There are
two, and §18.3 already did one of them (`ppair_matB`: the blocks of `matB t 0` are the top-level
subtrees).  This section does the other.

    dropLastB t      remove the LAST node in preorder
    matB_dropLast    and that is exactly `(matB t 0).dropLast`
    predP_matB       which is `Pred`, once the matrix has more than one column

`dropLastB` is the obvious recursion — drop the last child's last node, or the node itself when
it has no children — and the identity holds at every depth, which is what the recursion needs.
`sizeB_dropLast` is the measure going down by one; `nfLe_dropLast` keeps the class.

`sizeB_matB` ties the two sizes together (`(matB t d).length = sizeB t`), so `lenI` on the
matrix side is `sizeB` on the index side and the branch tests of `runAux` — `j1 == 0`, `isZeroP`
— become statements about the number of nodes. -/

section
open Trans.Recal
open Trans.Dict (BT)


/-! ### 最後の節を落とす -/

/-- 前順で最後の節を落とす。 -/
def dropLastB : B → B
  | .nil => .nil
  | .nd v r a => match a with
                 | .nil => r
                 | _ => .nd v r (dropLastB a)

theorem matB_dropLast : ∀ (t : B) (d : Nat),
    matB (dropLastB t) d = (matB t d).dropLast
  | .nil, _ => rfl
  | .nd v r a, d => by
      cases a with
      | nil =>
        show matB r d = ((matB r d ++ [[d, v]]).dropLast)
        rw [List.dropLast_concat]
      | nd u b c =>
        show matB (.nd v r (dropLastB (.nd u b c))) d
          = (matB r d ++ ([d, v] :: matB (.nd u b c) (d + 1))).dropLast
        rw [List.dropLast_append, if_neg (by simp)]
        show matB r d ++ ([d, v] :: matB (dropLastB (.nd u b c)) (d + 1))
          = matB r d ++ ([d, v] :: matB (.nd u b c) (d + 1)).dropLast
        rw [matB_dropLast (.nd u b c) (d + 1),
          show ([d, v] :: matB (.nd u b c) (d + 1)).dropLast
            = [d, v] :: (matB (.nd u b c) (d + 1)).dropLast from by
            rw [List.dropLast_cons_of_ne_nil (by
              show matB (.nd u b c) (d + 1) ≠ []
              intro hc
              exact absurd ((matB_eq_nil_iff _ (d + 1)).mp hc) (by
                intro hcc; exact B.noConfusion hcc))]]

theorem sizeB_dropLast : ∀ (t : B), t ≠ .nil → sizeB (dropLastB t) + 1 = sizeB t
  | .nil, h => absurd rfl h
  | .nd v r a, _ => by
      cases a with
      | nil => show sizeB r + 1 = sizeB r + 1 + sizeB (.nil : B); rfl
      | nd u b c =>
        show sizeB r + 1 + sizeB (dropLastB (.nd u b c)) + 1
          = sizeB r + 1 + sizeB (.nd u b c)
        rw [← sizeB_dropLast (.nd u b c) (by intro hc; exact B.noConfusion hc)]
        omega

theorem nfLe_dropLast : ∀ (t : B) (m : Nat), nfLe m t = true → nfLe m (dropLastB t) = true
  | .nil, _, _ => by rfl
  | .nd v r a, m, h => by
      obtain ⟨hv, hr, ha⟩ := (nfLe_nd_iff m v r a).mp h
      cases a with
      | nil => exact hr
      | nd u b c =>
        exact (nfLe_nd_iff m v r (dropLastB (.nd u b c))).mpr
          ⟨hv, hr, nfLe_dropLast (.nd u b c) (v + 1) ha⟩

theorem sizeB_matB : ∀ (t : B) (d : Nat), (matB t d).length = sizeB t
  | .nil, _ => rfl
  | .nd v r a, d => by
      rw [matB_len_nd]
      show _ = sizeB r + 1 + sizeB a
      rw [sizeB_matB r d, sizeB_matB a (d + 1)]

theorem lenI_matB (t : B) : lenI (psM (matB t 0)) = ((sizeB t : Nat) : Int) := by
  rw [lenI_psM]
  rw [sizeB_matB t 0]

/-- **`Pred` は「最後の節を落とす」。** 1 列のときは `Pred` は何もしない。 -/
theorem predP_matB (t : B) (h : 1 < sizeB t) :
    predP (psM (matB t 0)) = psM (matB (dropLastB t) 0) := by
  have hlen : (psM (matB t 0)).length = sizeB t := by
    rw [psM_len, sizeB_matB t 0]
  show (if (psM (matB t 0)).length == 1 then psM (matB t 0)
        else (psM (matB t 0)).dropLast) = _
  rw [show ((psM (matB t 0)).length == 1) = false from by
    rw [hlen]; exact decide_eq_false (by omega)]
  simp only [Bool.false_eq_true, if_false]
  show ((matB t 0).map _).dropLast = (matB (dropLastB t) 0).map _
  rw [matB_dropLast t 0, ← List.map_dropLast]

/-! ### 大きさが 1 の添字 -/

theorem sizeB_eq_zero : ∀ (t : B), sizeB t = 0 → t = .nil
  | .nil, _ => rfl
  | .nd _ r a, h => by
      have hh : sizeB r + 1 + sizeB a = 0 := h
      omega

theorem sizeB_eq_one : ∀ (t : B), sizeB t = 1 → ∃ v, t = .nd v .nil .nil
  | .nil, h => by
      have hh : (0 : Nat) = 1 := h
      omega
  | .nd v r a, h => by
      have hh : sizeB r + 1 + sizeB a = 1 := h
      refine ⟨v, ?_⟩
      rw [sizeB_eq_zero r (by omega), sizeB_eq_zero a (by omega)]

theorem isZeroP_matB_big (t : B) (h : 1 < sizeB t) : isZeroP (psM (matB t 0)) = false := by
  show ((psM (matB t 0)).length == 1 && _) = false
  rw [show ((psM (matB t 0)).length == 1) = false from by
    rw [psM_len, sizeB_matB t 0]
    exact decide_eq_false (by omega)]
  rfl

theorem isZeroP_matB_leaf : isZeroP (psM (matB (.nd 0 .nil .nil) 0)) = true := by decide

theorem bVal_leaf : bVal (.nd 0 .nil .nil) = .zero := by decide

end

/-! ## §52 THE FIRST BRANCH, AND THE MONAD

Two pieces of the induction, both independent of what `Trans` computes.

`runAux_leaf` is `runAux`'s `j1 == 0` branch on the index side.  Under `nfB` the only index with
one node is `nd 0 nil nil` — the root's level is forced to 0 — so the branch returns `zero`, and
that is `bVal` and `bMark` alike.  Both halves of the memo argument appear here in miniature:
a hit is discharged by `goodB_of_find`, a miss by `SoundB_cons` with §50's `goodB_mk`.

`mapM_run` is the monadic plumbing the several-blocks branch needs, and nothing in this
repository had it before: `runAux` runs the blocks with `List.mapM` in the state monad, so the
table each block sees is the one the previous block left.  The lemma threads that — given a
per-block statement that holds for EVERY sound table, the whole `mapM` returns the blocks'
values in order and leaves a sound table.  The induction is on the block list and the state
bookkeeping is just `List.mapM_cons`. -/

section
open Trans.Recal
open Trans.Dict (BT)


/-- 1 節の添字の行列。 -/
theorem psM_matB_leaf : psM (matB (.nd 0 .nil .nil) 0) = [((0 : Int), (0 : Int))] := rfl

theorem bValReq_leaf (req : Option Int) : bValReq (.nd 0 .nil .nil) req = .zero := by
  cases req with
  | none => rfl
  | some m => rfl

/-- memo に外れたときの 1 節の添字。 -/
theorem run_leaf_miss (f : Nat) (req : Option Int) (tbl : Trans.Recal.Memo)
    (h : tbl.find? (fun q => q.1 == (([((0 : Int), (0 : Int))] : Trans.Recal.PS), req))
      = none) :
    (Trans.Recal.runAux (f + 1) ([((0 : Int), (0 : Int))] : Trans.Recal.PS) req).run tbl
      = (BT.zero,
         ((([((0 : Int), (0 : Int))] : Trans.Recal.PS), req), BT.zero) :: tbl) := by
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, pure,
    get, getThe, MonadStateOf.get, h]
  rfl

/-- **`runAux` の型 -1 の枝。** 1 節の添字は `Trans` も `Mark` も 0。 -/
theorem runAux_leaf (g : Nat) (req : Option Int) (tbl : Trans.Recal.Memo)
    (hs : SoundB tbl) (ha : AllowedB (.nd 0 .nil .nil) req) :
    ((Trans.Recal.runAux (g + 1) (psM (matB (.nd 0 .nil .nil) 0)) req).run tbl).1
        = bValReq (.nd 0 .nil .nil) req
      ∧ SoundB ((Trans.Recal.runAux (g + 1) (psM (matB (.nd 0 .nil .nil) 0)) req).run tbl).2 := by
  rw [psM_matB_leaf, bValReq_leaf]
  cases hf : tbl.find? (fun z => z.1 == (([((0 : Int), (0 : Int))] : Trans.Recal.PS), req)) with
  | some p =>
    rw [runHit g _ req tbl p hf]
    obtain ⟨hg, he⟩ := goodB_of_find hs hf
    refine ⟨?_, hs⟩
    have hv := hg (.nd 0 .nil .nil) req (by decide) (by rw [psM_matB_leaf]; exact he) ha
    rw [hv, bValReq_leaf]
  | none =>
    rw [run_leaf_miss g req tbl hf]
    refine ⟨rfl, SoundB_cons hs ?_⟩
    have := goodB_mk (.nd 0 .nil .nil) req
    rw [psM_matB_leaf, bValReq_leaf] at this
    exact this

/-! ### ブロックを順に走らせる -/

theorem mapM_run (f : Nat) (val : Trans.Recal.PS → BT) :
    ∀ (Ms : List Trans.Recal.PS),
      (∀ M ∈ Ms, ∀ tbl : Trans.Recal.Memo, SoundB tbl →
          ((Trans.Recal.runAux f M none).run tbl).1 = val M
            ∧ SoundB ((Trans.Recal.runAux f M none).run tbl).2) →
      ∀ tbl : Trans.Recal.Memo, SoundB tbl →
        ((Ms.mapM (fun e => Trans.Recal.runAux f e none)).run tbl).1 = Ms.map val
          ∧ SoundB ((Ms.mapM (fun e => Trans.Recal.runAux f e none)).run tbl).2
  | [], _, tbl, hs => ⟨rfl, hs⟩
  | M :: rest, hstep, tbl, hs => by
      obtain ⟨hv1, hs1⟩ := hstep M (List.mem_cons_self ..) tbl hs
      obtain ⟨hv2, hs2⟩ := mapM_run f val rest
        (fun q hq => hstep q (List.mem_cons_of_mem M hq))
        ((Trans.Recal.runAux f M none).run tbl).2 hs1
      rw [List.mapM_cons]
      refine ⟨?_, ?_⟩
      · show ((Trans.Recal.runAux f M none).run tbl).1
            :: ((rest.mapM (fun e => Trans.Recal.runAux f e none)).run
                 ((Trans.Recal.runAux f M none).run tbl).2).1
          = val M :: rest.map val
        rw [hv1, hv2]
      · show SoundB ((rest.mapM (fun e => Trans.Recal.runAux f e none)).run
          ((Trans.Recal.runAux f M none).run tbl).2).2
        exact hs2

end

/-! ## §53 `bplus`, AND THE VALUES IT BUILDS

Every remaining branch of the induction ends in an equation between two `bplus` chains, so the
chains have to obey the laws one expects of a formal sum.  They almost do — `bplus a b` is
`ofL (a.toL ++ b.toL)`, which rebuilds the term from its components — but `ofL` is a section of
`toL` only on terms that ARE in that shape.  `BT.sum (BT.sum x y) z` is not, and neither is
anything with a `zero` inside.  So the laws carry a hypothesis:

    AtomsL t   every component of `t` is a `D` term
    NfSum t    `t` is what `ofL` gives back from its own components

    toL_bplus / atomsL_bplus / nfSum_bplus     `bplus` concatenates components and stays in shape
    bplus_zero_left / bplus_zero_right          unit, for terms in shape
    bplus_assoc                                 associativity, for atom-component terms

`AtomsL` is then discharged once and for all for the value functions: `bArg`, `bFold` and `bVal`
only ever `bplus` together `D` terms, so everything §48 and §49 produce is an atom list
(`atomsL_bArg_bFold`, `atomsL_bVal`), and the laws apply without side conditions from here on.

`mapM_run'` is §52's `mapM_run` in the form the several-blocks branch actually needs: the blocks
arrive as `(topSplit t).map (psM ∘ matB · 0)`, so the per-block hypothesis is stated about
indices, not about matrices, and no inverse of the encoding is needed. -/

section
open Trans.Recal
open Trans.Dict (BT)


/-! ### `bplus` の代数 -/

/-- 形式和の成分がすべて `D` であること。 -/
def AtomsL (t : BT) : Prop := ∀ x ∈ t.toL, ∃ u a, x = .D u a

/-- 成分から組み直して元へ戻ること (`ofL` の像に居ること)。 -/
def NfSum (t : BT) : Prop := BT.ofL t.toL = t

theorem atomsL_zero : AtomsL .zero := by
  intro x hx
  exact absurd hx (by simp [Trans.Dict.BT.toL])

theorem atomsL_D (u : Nat) (a : BT) : AtomsL (.D u a) := by
  intro x hx
  rw [List.mem_singleton.mp (show x ∈ [BT.D u a] from hx)]
  exact ⟨u, a, rfl⟩

theorem nfSum_zero : NfSum .zero := rfl

theorem nfSum_D (u : Nat) (a : BT) : NfSum (.D u a) := rfl

theorem toL_ofL : ∀ (l : List BT), (∀ x ∈ l, ∃ u a, x = .D u a) → (BT.ofL l).toL = l
  | [], _ => rfl
  | [x], h => by
      obtain ⟨u, a, rfl⟩ := h x (by simp)
      rfl
  | x :: y :: rest, h => by
      obtain ⟨u, a, rfl⟩ := h x (by simp)
      show ((BT.D u a).toL ++ (BT.ofL (y :: rest)).toL) = _
      rw [toL_ofL (y :: rest) (fun z hz => h z (List.mem_cons_of_mem _ hz))]
      rfl

theorem toL_bplus (a b : BT) (ha : AtomsL a) (hb : AtomsL b) :
    (bplus a b).toL = a.toL ++ b.toL := by
  show (BT.ofL (a.toL ++ b.toL)).toL = _
  refine toL_ofL _ (fun x hx => ?_)
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem atomsL_bplus (a b : BT) (ha : AtomsL a) (hb : AtomsL b) : AtomsL (bplus a b) := by
  intro x hx
  rw [toL_bplus a b ha hb] at hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem nfSum_bplus (a b : BT) (ha : AtomsL a) (hb : AtomsL b) : NfSum (bplus a b) := by
  show BT.ofL ((bplus a b).toL) = bplus a b
  rw [toL_bplus a b ha hb]
  rfl

theorem bplus_zero_left (b : BT) (hb : NfSum b) : bplus .zero b = b := by
  show BT.ofL ((BT.zero).toL ++ b.toL) = b
  rw [show (BT.zero).toL = ([] : List BT) from rfl, List.nil_append]
  exact hb

theorem bplus_zero_right (a : BT) (ha : NfSum a) : bplus a .zero = a := by
  show BT.ofL (a.toL ++ (BT.zero).toL) = a
  rw [show (BT.zero).toL = ([] : List BT) from rfl, List.append_nil]
  exact ha

theorem bplus_assoc (a b c : BT) (ha : AtomsL a) (hb : AtomsL b) (hc : AtomsL c) :
    bplus (bplus a b) c = bplus a (bplus b c) := by
  show BT.ofL ((bplus a b).toL ++ c.toL) = BT.ofL (a.toL ++ (bplus b c).toL)
  rw [toL_bplus a b ha hb, toL_bplus b c hb hc, List.append_assoc]

/-! ### ブロックを順に走らせる (添字の側) -/

theorem mapM_run' (f : Nat) (g : B → Trans.Recal.PS) (h : B → BT) :
    ∀ (ss : List B),
      (∀ s ∈ ss, ∀ tbl : Trans.Recal.Memo, SoundB tbl →
          ((Trans.Recal.runAux f (g s) none).run tbl).1 = h s
            ∧ SoundB ((Trans.Recal.runAux f (g s) none).run tbl).2) →
      ∀ tbl : Trans.Recal.Memo, SoundB tbl →
        (((ss.map g).mapM (fun e => Trans.Recal.runAux f e none)).run tbl).1 = ss.map h
          ∧ SoundB (((ss.map g).mapM (fun e => Trans.Recal.runAux f e none)).run tbl).2
  | [], _, tbl, hs => ⟨rfl, hs⟩
  | s :: rest, hstep, tbl, hs => by
      obtain ⟨hv1, hs1⟩ := hstep s (List.mem_cons_self ..) tbl hs
      obtain ⟨hv2, hs2⟩ := mapM_run' f g h rest
        (fun q hq => hstep q (List.mem_cons_of_mem s hq))
        ((Trans.Recal.runAux f (g s) none).run tbl).2 hs1
      show ((((g s) :: rest.map g).mapM (fun e => Trans.Recal.runAux f e none)).run tbl).1
          = h s :: rest.map h
        ∧ SoundB ((((g s) :: rest.map g).mapM
            (fun e => Trans.Recal.runAux f e none)).run tbl).2
      rw [List.mapM_cons]
      refine ⟨?_, ?_⟩
      · show ((Trans.Recal.runAux f (g s) none).run tbl).1
            :: (((rest.map g).mapM (fun e => Trans.Recal.runAux f e none)).run
                 ((Trans.Recal.runAux f (g s) none).run tbl).2).1
          = h s :: rest.map h
        rw [hv1, hv2]
      · show SoundB (((rest.map g).mapM (fun e => Trans.Recal.runAux f e none)).run
          ((Trans.Recal.runAux f (g s) none).run tbl).2).2
        exact hs2

/-! ### 値はいつも `D` の並び -/

theorem atomsL_bClose (w : Nat) (st : BT × Option BT) (h : AtomsL st.1) :
    AtomsL (bClose w st) := by
  show AtomsL (match st.2 with | none => st.1 | some a => bplus st.1 (.D w a))
  cases hst : st.2 with
  | none => exact h
  | some a => exact atomsL_bplus st.1 (.D w a) h (atomsL_D w a)

theorem atomsL_bArg_bFold : ∀ (s : B) (w : Nat),
    AtomsL (bArg w s) ∧ AtomsL ((bFold w s).1) := by
  intro s
  induction s with
  | nil => intro w; exact ⟨atomsL_zero, atomsL_zero⟩
  | nd u r c ihr ihc =>
    intro w
    have hK : AtomsL (if c == .nil then (.D u .zero : BT)
        else if u ≤ w || !(r == .nil) || headLvl c ≤ u then .D u (bArg u c)
        else bClose u (bFold u c)) := by
      by_cases h1 : c == .nil
      · rw [if_pos h1]; exact atomsL_D u .zero
      · rw [if_neg h1]
        by_cases h2 : u ≤ w || !(r == .nil) || headLvl c ≤ u
        · rw [if_pos h2]; exact atomsL_D u (bArg u c)
        · rw [if_neg h2]; exact atomsL_bClose u (bFold u c) (ihc u).2
    refine ⟨?_, ?_⟩
    · show AtomsL (bplus (bArg w r) _)
      exact atomsL_bplus _ _ (ihr w).1 hK
    · show AtomsL (
        (if w < u then (bplus (bClose w (bFold w r)) _, none)
         else match (bFold w r).2 with
              | none => ((bFold w r).1, some (bplus (bFold w r).1 _))
              | some a => ((bFold w r).1, some (bplus a _))).1)
      by_cases hw : w < u
      · rw [if_pos hw]
        exact atomsL_bplus _ _ (atomsL_bClose w (bFold w r) (ihr w).2) hK
      · rw [if_neg hw]
        cases hst : (bFold w r).2 with
        | none => exact (ihr w).2
        | some a => exact (ihr w).2

theorem atomsL_bVal : ∀ (t : B), AtomsL (bVal t)
  | .nil => atomsL_zero
  | .nd w r c => by
      show AtomsL (bplus (bVal r) (if r == .nil && w == 0 && c == .nil then .zero
        else .D w (bArg w c)))
      refine atomsL_bplus _ _ (atomsL_bVal r) ?_
      by_cases h : r == .nil && w == 0 && c == .nil
      · rw [if_pos h]; exact atomsL_zero
      · rw [if_neg h]; exact atomsL_D w (bArg w c)

end

/-! ## §54 THE SEVERAL-BLOCKS FOLD, ON BOTH SIDES

The `ppair` branch of `runAux` finishes by folding the blocks with an index-aware step: at
index 0 the accumulator is REPLACED by that block's value, and after that each block is
appended — as itself, or as `1` when the block is `(0,0)`.  Two lemmas make that shape usable.

`foldl_zipIdx_head` peels the special first step: once the index is positive it can never be
zero again (`foldl_zipIdx_pos`), so the whole thing is an ordinary `foldl` starting from the
first block's value.

`bVal_fold` says §48's `bVal` has exactly that shape.  It is defined by the right-nested
recursion `bplus (bVal r) (…)`, and `topSplit` appends the last top-level node, so the two line
up step for step: the first node contributes its own value — `zero` when it is `(0,0)`, which is
the `1 +` convention — and every later node contributes `topCB`, which is `psi_w(its argument)`
uniformly.  For a later `(0,0)` node that is `psi_0(0) = 1`, matching the algorithm's `bOne`.

So the two folds differ only in what they range over, and the several-blocks branch reduces to
the induction hypothesis applied block by block. -/

section
open Trans.Recal
open Trans.Dict (BT)


/-! ### 添字つきの畳み込み -/

theorem foldl_zipIdx_pos {α β : Type _} (op : β → α → β) (h : α → β) :
    ∀ (l : List α) (n : Nat), 0 < n → ∀ (init : β),
      (l.zipIdx n).foldl (fun a q => if q.2 == 0 then h q.1 else op a q.1) init
        = l.foldl op init
  | [], _, _, _ => rfl
  | x :: rest, n, hn, init => by
      show (rest.zipIdx (n + 1)).foldl (fun a q => if q.2 == 0 then h q.1 else op a q.1)
          (if (n == 0) = true then h x else op init x)
        = rest.foldl op (op init x)
      rw [if_neg (by
        intro hc
        have : n = 0 := of_decide_eq_true (by
          have := hc
          exact this)
        omega)]
      exact foldl_zipIdx_pos op h rest (n + 1) (by omega) (op init x)

theorem foldl_zipIdx_head {α β : Type _} (op : β → α → β) (h : α → β)
    (x : α) (rest : List α) (init : β) :
    ((x :: rest).zipIdx).foldl (fun a q => if q.2 == 0 then h q.1 else op a q.1) init
      = rest.foldl op (h x) := by
  show (rest.zipIdx 1).foldl (fun a q => if q.2 == 0 then h q.1 else op a q.1) (h x) = _
  exact foldl_zipIdx_pos op h rest 1 (by omega) (h x)

/-! ### `bVal` は最上位の節の畳み込み -/

/-- 最上位の節 1 つの寄与。 -/
def topCB : B → BT
  | .nil => .zero
  | .nd w _ c => .D w (bArg w c)

theorem topSplit_ne_nil : ∀ (t : B), t ≠ .nil → topSplit t ≠ []
  | .nil, h => absurd rfl h
  | .nd v r a, _ => by
      show topSplit r ++ [B.nd v .nil a] ≠ []
      intro hc
      have := congrArg List.length hc
      rw [List.length_append] at this
      simp at this

theorem bVal_fold : ∀ (t : B), t ≠ .nil →
    bVal t = ((topSplit t).drop 1).foldl (fun a s => bplus a (topCB s))
      (bVal ((topSplit t).getD 0 .nil))
  | .nil, h => absurd rfl h
  | .nd w r a, _ => by
      cases r with
      | nil => rfl
      | nd u b c =>
        have hne : (B.nd u b c) ≠ .nil := by intro hc; exact B.noConfusion hc
        have hts : topSplit (B.nd u b c) ≠ [] := topSplit_ne_nil _ hne
        have hih := bVal_fold (B.nd u b c) hne
        cases hq : topSplit (B.nd u b c) with
        | nil => exact absurd hq hts
        | cons y ys =>
          rw [hq] at hih
          show bplus (bVal (B.nd u b c))
              (if ((B.nd u b c) == .nil) && w == 0 && a == .nil then .zero
               else .D w (bArg w a))
            = ((topSplit (B.nd u b c) ++ [B.nd w .nil a]).drop 1).foldl
                (fun x s => bplus x (topCB s))
              (bVal ((topSplit (B.nd u b c) ++ [B.nd w .nil a]).getD 0 .nil))
          rw [hq, show ((y :: ys) ++ [B.nd w .nil a]).drop 1 = ys ++ [B.nd w .nil a] from rfl,
            show ((y :: ys) ++ [B.nd w .nil a]).getD 0 (.nil : B) = y from rfl,
            List.foldl_append,
            show ((y :: ys).drop 1).foldl (fun x s => bplus x (topCB s))
                (bVal ((y :: ys).getD 0 (.nil : B))) = ys.foldl
                (fun x s => bplus x (topCB s)) (bVal y) from rfl] at *
          rw [← hih,
            show (((B.nd u b c) == .nil) && w == 0 && a == .nil) = false from rfl]
          rfl

end

/-! ## §55 THE SEVERAL-BLOCKS BRANCH, PROVED

    runAux_sum : the `ppair` branch returns `bVal t`, and leaves the table sound

The first branch of the induction that actually computes something.  It is assembled from
what the last three sections built:

    run_sum_miss        unfold `runAux` past the memo miss, the reduction test (§47) and the
                        two branch tests, down to `mapM` followed by the fold
    ppair_matB (§18.3)  the blocks are the top-level subtrees
    mapM_run' (§53)     the induction hypothesis, applied block by block, threading the table
    sumFold_topSplit    the fold equals `bVal t` — §54's two halves meeting

`sumFold_topSplit` is where the work is.  `zip_map_pair` turns the algorithm's
`ps.zip rs` into one map over the subtrees, `foldl_zipIdx_head` removes the index, and
`topCB_eq` is the per-block identity: `if the block is (0,0) then 1 else its value` is
`psi_w(its argument)` either way, because `psi_0(0)` IS `1`.  That last equation is the only
place the `1 +` convention is handled, and it is handled once.

Nothing here depends on what `bArg` computes — only on `bVal` being a left fold over the
top-level nodes.  The branches that look inside `bArg` are the ones still to come. -/

section
open Trans.Recal
open Trans.Dict (BT)


/-- 型 -2 の枝が最後にやる畳み込み。 -/
def sumFold (ps : List Trans.Recal.PS) (rs : List BT) : BT :=
  ((ps.zip rs).zipIdx).foldl (init := BT.zero) fun a q =>
    if q.2 == 0 then q.1.2 else bplus a (if q.1.1 == zeroPS then bOne else q.1.2)

/-- memo に外れた型 -2 の枝。 -/
theorem run_sum_miss (f : Nat) (M : Trans.Recal.PS) (tbl : Trans.Recal.Memo)
    (hred : isReducedP M = true) (hj1 : (lenI M - 1 == 0) = false)
    (hprin : isPrincipalP M = false)
    (h : tbl.find? (fun q => q.1 == (M, (none : Option Int))) = none) :
    (Trans.Recal.runAux (f + 1) M none).run tbl
      = (sumFold (ppair M)
            (((ppair M).mapM (fun e => Trans.Recal.runAux f e none)).run tbl).1,
         ((M, (none : Option Int)),
            sumFold (ppair M)
              (((ppair M).mapM (fun e => Trans.Recal.runAux f e none)).run tbl).1)
           :: (((ppair M).mapM (fun e => Trans.Recal.runAux f e none)).run tbl).2) := by
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, pure,
    get, getThe, MonadStateOf.get, h, hred, hj1, hprin,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true]
  rfl

/-! ### 枝の組み立て -/

theorem zip_map_pair {α β γ : Type _} (g : α → β) (h : α → γ) :
    ∀ (l : List α), (l.map g).zip (l.map h) = l.map (fun x => (g x, h x))
  | [] => rfl
  | x :: rest => by
      show (g x, h x) :: (rest.map g).zip (rest.map h) = _
      rw [zip_map_pair g h rest]
      rfl

theorem topSplit_shape : ∀ (t : B), ∀ s ∈ topSplit t, ∃ w c, s = .nd w .nil c
  | .nil, s, hs => absurd hs (by simp [topSplit])
  | .nd v r a, s, hs => by
      rcases List.mem_append.mp hs with h | h
      · exact topSplit_shape r s h
      · exact ⟨v, a, List.mem_singleton.mp h⟩

theorem psM_matB_eq_zeroPS (w : Nat) (c : B) :
    (psM (matB (.nd w .nil c) 0) == zeroPS) = (w == 0 && c == .nil) := by
  cases c with
  | nil =>
    cases w with
    | zero => rfl
    | succ k => rfl
  | nd u b d =>
    have hlen : (psM (matB (.nd w .nil (.nd u b d)) 0)).length = sizeB (.nd w .nil (.nd u b d)) := by
      rw [psM_len, sizeB_matB]
    have hpos : 1 < (psM (matB (.nd w .nil (.nd u b d)) 0)).length := by
      rw [hlen]
      show 1 < sizeB (.nil : B) + 1 + sizeB (B.nd u b d)
      show 1 < 0 + 1 + (sizeB b + 1 + sizeB d)
      omega
    rw [show ((B.nd u b d) == (.nil : B)) = false from rfl, Bool.and_false]
    refine Bool.eq_false_iff.mpr (fun hc => ?_)
    have := congrArg List.length (eq_of_beq hc)
    show False
    have hz : (zeroPS : Trans.Recal.PS).length = 1 := rfl
    omega

theorem topCB_eq (w : Nat) (c : B) :
    (if (psM (matB (.nd w .nil c) 0) == zeroPS) then bOne else bVal (.nd w .nil c))
      = topCB (.nd w .nil c) := by
  rw [psM_matB_eq_zeroPS w c]
  by_cases h : w == 0 && c == .nil
  · rw [if_pos h]
    have hw : w = 0 := of_decide_eq_true (by
      have := (Bool.and_eq_true _ _).mp h
      exact this.1)
    have hc : c = .nil := eq_of_beq ((Bool.and_eq_true _ _).mp h).2
    subst hw; subst hc
    rfl
  · rw [if_neg h]
    show bplus (bVal .nil) (if ((.nil : B) == .nil) && w == 0 && c == .nil then .zero
      else .D w (bArg w c)) = .D w (bArg w c)
    rw [show (((.nil : B) == .nil) && w == 0 && c == .nil) = false from by
      rw [show ((.nil : B) == (.nil : B)) = true from rfl, Bool.true_and]
      exact Bool.eq_false_iff.mpr h]
    simp only [Bool.false_eq_true, if_false]
    exact bplus_zero_left _ (nfSum_D w (bArg w c))

theorem foldl_congr_mem {α β : Type _} (f g : β → α → β) :
    ∀ (l : List α), (∀ x ∈ l, ∀ a, f a x = g a x) → ∀ init, l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: rest, h, init => by
      show rest.foldl f (f init x) = rest.foldl g (g init x)
      rw [h x (List.mem_cons_self ..) init]
      exact foldl_congr_mem f g rest (fun y hy => h y (List.mem_cons_of_mem x hy)) (g init x)

/-- **アルゴリズムの畳み込みは `bVal`。** -/
theorem sumFold_topSplit (t : B) (hne : t ≠ .nil) :
    sumFold ((topSplit t).map (fun s => psM (matB s 0))) ((topSplit t).map bVal) = bVal t := by
  have hsh := topSplit_shape t
  cases hq : topSplit t with
  | nil => exact absurd hq (topSplit_ne_nil t hne)
  | cons s0 rest =>
    have hb := bVal_fold t hne
    rw [hq] at hb
    show ((((s0 :: rest).map (fun s => psM (matB s 0))).zip
        ((s0 :: rest).map bVal)).zipIdx).foldl
        (init := BT.zero) (fun a q =>
          if q.2 == 0 then q.1.2 else bplus a (if q.1.1 == zeroPS then bOne else q.1.2)) = _
    rw [zip_map_pair (fun s => psM (matB s 0)) bVal (s0 :: rest),
      show ((s0 :: rest).map (fun s => (psM (matB s 0), bVal s)))
        = (psM (matB s0 0), bVal s0) :: (rest.map (fun s => (psM (matB s 0), bVal s))) from rfl,
      foldl_zipIdx_head
        (fun (a : BT) (q : Trans.Recal.PS × BT) =>
          bplus a (if q.1 == zeroPS then bOne else q.2))
        (fun (q : Trans.Recal.PS × BT) => q.2)
        (psM (matB s0 0), bVal s0) (rest.map (fun s => (psM (matB s 0), bVal s))) BT.zero,
      List.foldl_map,
      foldl_congr_mem
        (fun (a : BT) (s : B) => bplus a (if psM (matB s 0) == zeroPS then bOne else bVal s))
        (fun (a : BT) (s : B) => bplus a (topCB s)) rest
        (fun x hx a => by
          obtain ⟨w, c, rfl⟩ := hsh x (by rw [hq]; exact List.mem_cons_of_mem s0 hx)
          show bplus a (if (psM (matB (B.nd w .nil c) 0) == zeroPS) then bOne
              else bVal (B.nd w .nil c)) = bplus a (topCB (B.nd w .nil c))
          rw [topCB_eq w c])]
    show rest.foldl (fun a s => bplus a (topCB s)) (bVal s0) = _
    rw [hb]
    rfl

/-- **`runAux` の型 -2 の枝** (要求は `Trans`)。 -/
theorem runAux_sum (g : Nat) (t : B) (hnf : nfB t = true) (hne : t ≠ .nil)
    (hj1 : (lenI (psM (matB t 0)) - 1 == 0) = false)
    (hprin : isPrincipalP (psM (matB t 0)) = false)
    (tbl : Trans.Recal.Memo) (hs : SoundB tbl)
    (ih : ∀ s ∈ topSplit t, ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB s 0)) none).run tb).1 = bVal s
          ∧ SoundB ((Trans.Recal.runAux g (psM (matB s 0)) none).run tb).2) :
    ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) none).run tbl).1 = bVal t
      ∧ SoundB ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) none).run tbl).2 := by
  cases hf : tbl.find? (fun z => z.1 == (psM (matB t 0), (none : Option Int))) with
  | some p =>
    rw [runHit g _ none tbl p hf]
    obtain ⟨hg, he⟩ := goodB_of_find hs hf
    exact ⟨hg t none hnf he (Or.inl rfl), hs⟩
  | none =>
    rw [run_sum_miss g (psM (matB t 0)) tbl (isReducedP_matB t hnf) hj1 hprin hf,
      ppair_matB t]
    obtain ⟨hv, hsd⟩ := mapM_run' g (fun s => psM (matB s 0)) bVal (topSplit t) ih tbl hs
    rw [hv, sumFold_topSplit t hne]
    exact ⟨rfl, SoundB_cons hsd (goodB_mk t none)⟩

end

/-! ## §56 THE TYPE-0 BRANCH, PROVED

    runAux_type0       the `t1 == 0` branch returns `bVal t`, and leaves the table sound
    runAux_type0_mark  the same branch for `Mark m`, returning `bMark t m`

§55 did the several-blocks branch; this is the other branch that closes without looking inside
`replMark`.  `runAux` reaches it when the index is reduced, has more than one column, is
principal, and the recursive call on `Pred` comes back `0`.  The pieces:

    bVal_eq_zero_iff    §53's `bplus` algebra, read backwards: a value is `0` only when it has
                        no components, and `bVal` drops a component only for the leading `(0,0)`
    type0_shape         so the hypotheses pin the index completely — the branch is reached by
                        `(0,0)(1,u)` and nothing else
    run_zero_miss       unfold `runAux` past the memo miss and the four tests, down to the
                        returned value and the pushed entry (§55's `run_sum_miss`, one test
                        deeper)

WHY THE SHAPE IS THE WHOLE CONTENT.  `bVal (dropLastB t) = 0` forces `dropLastB t` to be the
one-node `(0,0)` (it cannot be empty, since `t` has at least two nodes), so `t` has exactly two
nodes.  Two nodes and `nfB` leave two candidates — `(0,0)(1,u)` and `(0,0)(0,0)` — and
`isPrincipalP` kills the second: its last column has no row-0 ancestor.  What is left is a
family in `u` on which both sides are closed computations, so `bVal`, `bMark`, `gp1` and the
branch tests all reduce and the two halves are `rfl`.

The `Mark` half needs one extra fact and no extra work: `lastSpine ((0,0)(1,u))` is `[0,1]`, so
`AllowedB` leaves only `m = 0` (the collapsed root, which is the value) and `m = 1` (the last
column, which is `psi_u(0)`) — exactly the algorithm's `if m == 0` split. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### 値が 0 になる添字 -/

/-- 成分から組み直せる項は、成分が無いときに限り `0`。 -/
theorem eq_zero_iff_toL (a : BT) (h : NfSum a) : a = BT.zero ↔ a.toL = [] := by
  constructor
  · intro hz
    rw [hz]
    rfl
  · intro hl
    have : BT.ofL a.toL = a := h
    rw [hl] at this
    exact this.symm

theorem nfSum_bVal : ∀ (t : B), NfSum (bVal t)
  | .nil => nfSum_zero
  | .nd w r c => by
      show NfSum (bplus (bVal r) (if r == .nil && w == 0 && c == .nil then .zero
        else .D w (bArg w c)))
      refine nfSum_bplus _ _ (atomsL_bVal r) ?_
      by_cases h : r == .nil && w == 0 && c == .nil
      · rw [if_pos h]; exact atomsL_zero
      · rw [if_neg h]; exact atomsL_D w (bArg w c)

/-- **値が 0 になる添字は 2 つだけ。** 空か、1 節の `(0,0)` か。 -/
theorem bVal_eq_zero_iff (s : B) (_hnf : nfB s = true) :
    bVal s = BT.zero ↔ (s = .nil ∨ s = .nd 0 .nil .nil) := by
  cases s with
  | nil => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | nd w r c =>
    have hK : AtomsL (if r == .nil && w == 0 && c == .nil then (.zero : BT)
        else .D w (bArg w c)) := by
      by_cases h : r == .nil && w == 0 && c == .nil
      · rw [if_pos h]; exact atomsL_zero
      · rw [if_neg h]; exact atomsL_D w (bArg w c)
    have htoL : (bVal (.nd w r c)).toL
        = (bVal r).toL ++ (if r == .nil && w == 0 && c == .nil then (.zero : BT)
            else .D w (bArg w c)).toL := by
      show (bplus (bVal r) _).toL = _
      exact toL_bplus _ _ (atomsL_bVal r) hK
    constructor
    · intro hz
      have h0 : (bVal (.nd w r c)).toL = [] :=
        (eq_zero_iff_toL _ (nfSum_bVal (.nd w r c))).mp hz
      rw [htoL] at h0
      have hK0 : (if r == .nil && w == 0 && c == .nil then (.zero : BT)
          else .D w (bArg w c)).toL = [] := (List.append_eq_nil_iff.mp h0).2
      have hcond : (r == .nil && w == 0 && c == .nil) = true := by
        cases hc : (r == .nil && w == 0 && c == .nil) with
        | true => rfl
        | false =>
          exfalso
          rw [hc, if_neg (show ¬((false : Bool) = true) from by
            intro hcc; exact Bool.noConfusion hcc)] at hK0
          have hbad : ([BT.D w (bArg w c)] : List BT) = [] := hK0
          cases hbad
      refine Or.inr ?_
      have h1 := (Bool.and_eq_true _ _).mp hcond
      have h2 := (Bool.and_eq_true _ _).mp h1.1
      rw [eq_of_beq h2.1, eq_of_beq h1.2, eq_of_beq h2.2]
    · intro h
      rcases h with h | h
      · exact absurd h (by intro hc; exact B.noConfusion hc)
      · rw [h]
        exact bVal_leaf

/-! ### memo に外れた型 0 の枝 -/

/-- 型 0 の枝が返す値。 -/
def zeroAns (M : Trans.Recal.PS) (req : Option Int) : BT :=
  match req with
  | none => BT.D 0 (BT.D (gp1 M (lenI M - 1)).toNat BT.zero)
  | some m => if m == 0 then BT.D 0 (BT.D (gp1 M (lenI M - 1)).toNat BT.zero)
              else BT.D (gp1 M (lenI M - 1)).toNat BT.zero

/-- memo に外れた型 0 の枝。 -/
theorem run_zero_miss (f : Nat) (M : Trans.Recal.PS) (req : Option Int)
    (tbl : Trans.Recal.Memo)
    (hred : isReducedP M = true) (hj1 : (lenI M - 1 == 0) = false)
    (hprin : isPrincipalP M = true)
    (hz : ((Trans.Recal.runAux f (predP M) none).run tbl).1 = BT.zero)
    (h : tbl.find? (fun q => q.1 == (M, req)) = none) :
    (Trans.Recal.runAux (f + 1) M req).run tbl
      = (zeroAns M req,
         ((M, req), zeroAns M req)
           :: ((Trans.Recal.runAux f (predP M) none).run tbl).2) := by
  have hz' : Trans.Recal.runAux f (predP M) none tbl
      = (BT.zero, (Trans.Recal.runAux f (predP M) none tbl).2) := by
    rw [← hz]
    rfl
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, pure,
    get, getThe, MonadStateOf.get, h, hred, hj1, hprin,
    Bool.not_true, Bool.false_eq_true, if_false]
  rw [hz']
  cases req with
  | none => rfl
  | some m => rfl

/-! ### 型 0 に落ちる添字の形 -/

-- 測定: `(0,0)(0,0)` は principal ではない。上の場合分けで消えるのはこれ。
#guard isPrincipalP (psM (matB (.nd 0 (.nd 0 .nil .nil) .nil) 0)) == false

/-- **型 0 の枝に来る添字は 2 節の `(0,0)(1,u)` しかない。** -/
theorem type0_shape (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true)
    (hz : bVal (dropLastB t) = BT.zero) :
    ∃ u, t = .nd 0 .nil (.nd u .nil .nil) := by
  have hne : t ≠ .nil := by
    intro hc
    rw [hc] at h1
    have : sizeB (.nil : B) = 0 := rfl
    omega
  have hsz := sizeB_dropLast t hne
  have hdnf : nfB (dropLastB t) = true := nfLe_dropLast t 0 hnf
  have hd2 : dropLastB t = .nd 0 .nil .nil := by
    rcases (bVal_eq_zero_iff _ hdnf).mp hz with h | h
    · exfalso
      rw [h] at hsz
      have : sizeB (.nil : B) = 0 := rfl
      omega
    · exact h
  have hsz2 : sizeB t = 2 := by
    rw [hd2] at hsz
    have : sizeB (.nd 0 .nil .nil : B) = 1 := rfl
    omega
  cases t with
  | nil => exact absurd rfl hne
  | nd v r a =>
    obtain ⟨hv, hrnf, hanf⟩ := (nfLe_nd_iff 0 v r a).mp hnf
    have hv0 : v = 0 := by omega
    subst hv0
    have hs : sizeB r + 1 + sizeB a = 2 := hsz2
    cases a with
    | nil =>
      exfalso
      have hr : r = .nd 0 .nil .nil := hd2
      rw [hr] at hprin
      exact absurd hprin (by decide)
    | nd u b c =>
      have hac : sizeB (B.nd u b c) = sizeB b + 1 + sizeB c := rfl
      refine ⟨u, ?_⟩
      rw [sizeB_eq_zero r (by omega), sizeB_eq_zero b (by omega),
        sizeB_eq_zero c (by omega)]

/-! ### 型 0 の枝、`Trans` の側 -/

/-- 型 0 の添字の行列。 -/
theorem psM_matB_type0 (u : Nat) :
    psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0)
      = [((0 : Int), (0 : Int)), ((1 : Int), ((u : Nat) : Int))] := rfl

theorem lenI_type0 (u : Nat) :
    (lenI (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0)) - 1 == 0) = false := rfl

theorem bVal_type0 (u : Nat) :
    bVal (.nd 0 .nil (.nd u .nil .nil)) = BT.D 0 (BT.D u BT.zero) := rfl

theorem zeroAns_type0 (u : Nat) :
    zeroAns (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0)) none
      = BT.D 0 (BT.D u BT.zero) := rfl

/-- **`runAux` の型 0 の枝** (要求は `Trans`)。 -/
theorem runAux_type0 (g : Nat) (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true)
    (hzv : bVal (dropLastB t) = BT.zero)
    (tbl : Trans.Recal.Memo) (hs : SoundB tbl)
    (ih : ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tb).1
            = bVal (dropLastB t)
          ∧ SoundB ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tb).2) :
    ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) none).run tbl).1 = bVal t
      ∧ SoundB ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) none).run tbl).2 := by
  obtain ⟨u, ht⟩ := type0_shape t hnf h1 hprin hzv
  subst ht
  cases hf : tbl.find? (fun z =>
      z.1 == (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0), (none : Option Int))) with
  | some p =>
    rw [runHit g _ none tbl p hf]
    obtain ⟨hg, he⟩ := goodB_of_find hs hf
    exact ⟨hg _ none hnf he (Or.inl rfl), hs⟩
  | none =>
    obtain ⟨hv, hsd⟩ := ih tbl hs
    rw [hzv] at hv
    have hzr : ((Trans.Recal.runAux g
        (predP (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0))) none).run tbl).1 = BT.zero := by
      rw [predP_matB _ h1]
      exact hv
    have hsd' : SoundB ((Trans.Recal.runAux g
        (predP (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0))) none).run tbl).2 := by
      rw [predP_matB _ h1]
      exact hsd
    rw [run_zero_miss g _ none tbl (isReducedP_matB _ hnf) (lenI_type0 u) hprin hzr hf,
      zeroAns_type0 u, bVal_type0 u]
    exact ⟨rfl, SoundB_cons hsd' (by
      have := goodB_mk (.nd 0 .nil (.nd u .nil .nil)) none
      rw [show bValReq (.nd 0 .nil (.nd u .nil .nil)) none = BT.D 0 (BT.D u BT.zero) from rfl]
        at this
      exact this)⟩

/-! ### 型 0 の枝、`Mark` の側 -/

theorem lastSpine_type0 (u : Nat) : lastSpine (.nd 0 .nil (.nd u .nil .nil)) = [0, 1] := rfl

/-- 型 0 の添字で意味を持つ `Mark` の位置は 0 と 1 だけ。 -/
theorem markOKB_type0 (u k : Nat) (h : markOKB (.nd 0 .nil (.nd u .nil .nil)) k = true) :
    k = 0 ∨ k = 1 := by
  have hmem : (decide (k ∈ lastSpine (.nd 0 .nil (.nd u .nil .nil)))) = true :=
    ((Bool.and_eq_true _ _).mp h).1
  rw [lastSpine_type0] at hmem
  have hk : k ∈ [0, 1] := of_decide_eq_true hmem
  rcases List.mem_cons.mp hk with h0 | h1
  · exact Or.inl h0
  · rcases List.mem_cons.mp h1 with h2 | h3
    · exact Or.inr h2
    · exact absurd h3 (by intro hc; cases hc)

theorem zeroAns_type0_mark (u k : Nat) (hk : k = 0 ∨ k = 1) :
    zeroAns (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0)) (some ((k : Nat) : Int))
      = bValReq (.nd 0 .nil (.nd u .nil .nil)) (some ((k : Nat) : Int)) := by
  rcases hk with h | h
  · subst h; rfl
  · subst h; rfl

/-- **`runAux` の型 0 の枝** (要求は `Mark m`)。 -/
theorem runAux_type0_mark (g : Nat) (t : B) (m : Int) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true)
    (hzv : bVal (dropLastB t) = BT.zero)
    (hal : AllowedB t (some m))
    (tbl : Trans.Recal.Memo) (hs : SoundB tbl)
    (ih : ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tb).1
            = bVal (dropLastB t)
          ∧ SoundB ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tb).2) :
    ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) (some m)).run tbl).1
        = bValReq t (some m)
      ∧ SoundB ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) (some m)).run tbl).2 := by
  obtain ⟨u, ht⟩ := type0_shape t hnf h1 hprin hzv
  subst ht
  obtain ⟨k, hkm, hkok⟩ : ∃ k : Nat, (some m : Option Int) = some ((k : Nat) : Int)
      ∧ markOKB (.nd 0 .nil (.nd u .nil .nil)) k = true := by
    rcases hal with h | h
    · exact absurd h (by intro hc; cases hc)
    · exact h
  have hm : m = ((k : Nat) : Int) := Option.some.inj hkm
  subst hm
  cases hf : tbl.find? (fun z =>
      z.1 == (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0),
              (some ((k : Nat) : Int) : Option Int))) with
  | some p =>
    rw [runHit g _ (some ((k : Nat) : Int)) tbl p hf]
    obtain ⟨hg, he⟩ := goodB_of_find hs hf
    exact ⟨hg _ (some ((k : Nat) : Int)) hnf he (Or.inr ⟨k, rfl, hkok⟩), hs⟩
  | none =>
    obtain ⟨hv, hsd⟩ := ih tbl hs
    rw [hzv] at hv
    have hzr : ((Trans.Recal.runAux g
        (predP (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0))) none).run tbl).1 = BT.zero := by
      rw [predP_matB _ h1]
      exact hv
    have hsd' : SoundB ((Trans.Recal.runAux g
        (predP (psM (matB (.nd 0 .nil (.nd u .nil .nil)) 0))) none).run tbl).2 := by
      rw [predP_matB _ h1]
      exact hsd
    rw [run_zero_miss g _ (some ((k : Nat) : Int)) tbl (isReducedP_matB _ hnf)
        (lenI_type0 u) hprin hzr hf,
      zeroAns_type0_mark u k (markOKB_type0 u k hkok)]
    exact ⟨rfl, SoundB_cons hsd' (goodB_mk (.nd 0 .nil (.nd u .nil .nil))
      (some ((k : Nat) : Int)))⟩

/-! ### 測定 -/

-- 型 0 の枝に落ちる標準形の添字は、この 2 つだけ (段 < 4、8 節まで)。
#guard ((popNFB 4 8).filter fun t =>
    1 < sizeB t && isPrincipalP (psM (matB t 0)) && (bVal (dropLastB t) == BT.zero))
  == [.nd 0 .nil (.nd 0 .nil .nil), .nd 0 .nil (.nd 1 .nil .nil)]
-- 参照実装の `Trans` と `Mark` は、その 2 つで §48・§49 の閉じた形と合う。
#guard (([.nd 0 .nil (.nd 0 .nil .nil), .nd 0 .nil (.nd 1 .nil .nil)] : List B)).all fun t =>
  transPort (psM (matB t 0)) == bVal t
#guard (([.nd 0 .nil (.nd 0 .nil .nil), .nd 0 .nil (.nd 1 .nil .nil)] : List B)).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m) || markRun (psM (matB t 0)) (Int.ofNat m) == bMark t m

end

end Evidence.Region
