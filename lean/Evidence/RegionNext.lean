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

PROVED IN §60.  When this section was written everything here was measured; the proof went
through `runAux`'s memo table, the way `Rows/G3`, `G4` and `G11` did for their ladders — `bVal`
is what their `Val` was per family, written once for the whole region — and closed in §60 as
`transPort_bVal`.  The guards below are kept as the record of what was measured first. -/

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

PROVED IN §60, like §48 (`markRun_bMark`).  Together the two give the `Val` of a `Good`/`Sound`
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

/-! ## §57 THE BRANCH DATA OF TYPES 1-6, ON THE INDEX SIDE

    fpar_last_spine      j0  is the TREE PARENT of the last node
    isAdm_tree           isAdm is a completely local test on two consecutive columns
    adm_tree             adm  is the obvious downward recursion on the index side
    transTypeMain_tree   the type is read off the levels of `j0` and `j1`
    run_main_miss_*      the plumbing: unfold `runAux` into the types 1-6 body

§55 proved the several-blocks branch and §56 the type-0 branch.  What is left of `runAux` is
the types 1-6 branch, and before its VALUE can be discussed at all its four inputs have to be
named on the index side.  `runAux` computes them off the MATRIX:

    j1  = lenI M - 1                the last column
    j0  = fpar M 0 j1 0             its row-0 parent
    ty  = transTypeMain M j0 j1     the case number
    jn1 = adm M j0                  the mark the recursive call will ask for

and this section says what each of them is when `M = psM (matB t 0)`.

WHAT CARRIES EACH ONE.

`j0` is the only one with content.  `fpar M 0 j 0` is BMS's `parent` (§18.1's
`fpar0_eq_parent`), so the question is what the row-0 parent of the LAST column of a `matB`
matrix is, and the answer is the tree one: the second-to-last entry of `lastSpine t` — the
chain "last top-level node, its last child, and so on" that §49 already uses to say where
`Mark` means anything.  `parent_lastSpine` proves it by the file's usual three-way split.  The
`a = nil` case is the one where the last node sits at depth `d`, so nothing before it is
shallower and there is no parent — which is also the case `isPrincipalP` rules out.  In the
other case the node's own column (index `sizeB r`, depth `d`) is always a candidate, so the
maximum is either that column or, when the argument has a parent of its own, the translate of
the argument's answer; and that is exactly what `dropLast`/`getLast?` do to the spine.

`isAdm` needs NO normal form and no principality: §26's `isParentP_succ_iff` is unconditional
and says `isParentP M 1 (j+1) j` is "depth and level both go up", so `isUnadmitted` is that
test at `j-1` and at `j` and nothing else.  The two edges are `isParentP_succ_oob` (no column
to the right) and the `0 ≤ k` guard of `isParentP` (no column to the left of `0`); note the
`j + 1 < sizeB t` conjunct of `isAdmB` is REDUNDANT — past the end `ent` reads as `0`, so
`bothInc` is already false there — and is kept only because that is the measured spelling.
The one hypothesis that cannot be dropped is `j ≤ sizeB t`: `isUnadmitted` opens with
`decide (j > lenI M)`, so beyond the matrix the two sides genuinely differ.

`adm` and `transTypeMain` are then mechanical: `adm` is `admAux`'s fuelled downward scan,
which is the index-side `admB` recursion once `isAdm` is local, and `transTypeMain` is a
three-way test on `gp1`, which is `entL` through `psM_gp1`.

WHAT IS NOT CLAIMED.  Nothing here evaluates the branch.  The step from these four data to
`bVal t` goes through `replMark`, and that equation — `bMark s jn1` occurs on the rightmost
spine of `bVal s`, and replacing it by `c2` gives `bVal t` — is MEASURED at the end of the
section and is the next section's job.  `run_main_miss_none` / `_mark_lt` / `_mark_ge` are the
same unfolding §55 and §56 did, one and two tests deeper, and are stated so that the next
section can quote them without re-deriving the monad. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### 行 0 の親の道具 -/

/-- `parent M 0 x` を「最大」の仕様から作る。 -/
theorem parent0_eq_some (M : Matrix) (x q : Nat) (hq : q < x)
    (hlt : ent M q 0 < ent M x 0)
    (hmax : ∀ p, q < p → p < x → ent M x 0 ≤ ent M p 0) :
    parent M 0 x = some q := by
  show ((List.range x).filter (fun p => decide (ent M p 0 < ent M x 0))).max? = some q
  refine List.max?_eq_some_iff.mpr ⟨List.mem_filter.mpr
    ⟨List.mem_range.mpr hq, decide_eq_true hlt⟩, ?_⟩
  intro b hb
  have hb1 := List.mem_range.mp (List.mem_filter.mp hb).1
  have hb2 := of_decide_eq_true (List.mem_filter.mp hb).2
  rcases Nat.lt_or_ge q b with hlt2 | hge
  · exact absurd (hmax b hlt2 hb1) (by omega)
  · exact hge

/-- 親が無いなら自分が左極小。 -/
theorem min_of_parent0_none (M : Matrix) (x : Nat) (h : parent M 0 x = none) :
    ∀ i, i < x → ent M x 0 ≤ ent M i 0 := by
  intro i hi
  rcases Nat.lt_or_ge (ent M i 0) (ent M x 0) with hc | hc
  · exfalso
    have hmem : i ∈ (List.range x).filter (fun p => decide (ent M p 0 < ent M x 0)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hi, decide_eq_true hc⟩
    rw [List.max?_eq_none_iff.mp h] at hmem
    exact absurd hmem (by simp)
  · exact hc

/-! ### `matB` の三分割で成分を読む -/

theorem ent_nd_left (v : Nat) (r a : B) (d p y : Nat) (h : p < sizeB r) :
    ent (matB (.nd v r a) d) p y = ent (matB r d) p y :=
  ent_append_left (matB r d) _ p y (by rw [sizeB_matB]; exact h)

theorem ent_nd_node (v : Nat) (r a : B) (d y : Nat) :
    ent (matB (.nd v r a) d) (sizeB r) y = ([d, v] : Col).getD y 0 := by
  show ent (matB r d ++ ([d, v] :: matB a (d + 1))) (sizeB r) y = _
  rw [ent_append (matB r d) _ _ y (by rw [sizeB_matB]; omega), sizeB_matB,
    show sizeB r - sizeB r = 0 from by omega]
  rfl

theorem ent_nd_right (v : Nat) (r a : B) (d i y : Nat) :
    ent (matB (.nd v r a) d) (sizeB r + 1 + i) y = ent (matB a (d + 1)) i y := by
  show ent (matB r d ++ ([d, v] :: matB a (d + 1))) (sizeB r + 1 + i) y = _
  rw [ent_append (matB r d) _ _ y (by rw [sizeB_matB]; omega), sizeB_matB,
    show sizeB r + 1 + i - sizeB r = i + 1 from by omega]
  show ((([d, v] :: matB a (d + 1)).getD (i + 1) []).getD y 0) = _
  rw [show (([d, v] :: matB a (d + 1)).getD (i + 1) []) = (matB a (d + 1)).getD i [] from by
    simp [List.getD_eq_getElem?_getD]]
  rfl

/-- `matB t d` のどの列も深さ `d` 以上。 -/
theorem ent_lb (t : B) (d p : Nat) (h : p < sizeB t) : d ≤ ent (matB t d) p 0 :=
  matB_col_lb t d _ (getD_mem (matB t d) [] p (by rw [sizeB_matB]; exact h))

theorem sizeB_pos (t : B) (h : t ≠ .nil) : 0 < sizeB t := by
  cases t with
  | nil => exact absurd rfl h
  | nd u b c => show 0 < sizeB b + 1 + sizeB c; omega

theorem lastSpine_ne_nil (t : B) (h : t ≠ .nil) : lastSpine t ≠ [] := by
  cases t with
  | nil => exact absurd rfl h
  | nd u b c =>
    show (sizeB b :: (lastSpine c).map (fun i => sizeB b + 1 + i)) ≠ []
    exact List.cons_ne_nil _ _

/-! ### 1. 最後の列の行 0 の親は木の親 -/

/-- **最後の列の行 0 の親は、祖先鎖の最後から 2 番目。** -/
theorem parent_lastSpine : ∀ (t : B), t ≠ .nil → ∀ (d : Nat),
    parent (matB t d) 0 (sizeB t - 1) = ((lastSpine t).dropLast).getLast? := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | nd v r a _ iha =>
    intro _ d
    cases a with
    | nil =>
      have hsz : sizeB (B.nd v r .nil) - 1 = sizeB r := by
        show sizeB r + 1 + sizeB (.nil : B) - 1 = sizeB r
        show sizeB r + 1 + 0 - 1 = sizeB r
        omega
      rw [hsz, show ((lastSpine (B.nd v r .nil)).dropLast).getLast? = none from rfl]
      refine parent0_none_of_min _ _ ?_
      intro i hi
      rw [ent_nd_node v r .nil d 0, ent_nd_left v r .nil d i 0 hi]
      exact ent_lb r d i hi
    | nd u b c =>
      have hAne : (B.nd u b c) ≠ .nil := by intro hc; exact B.noConfusion hc
      have hN : 0 < sizeB (B.nd u b c) := sizeB_pos _ hAne
      have hsz : sizeB (B.nd v r (.nd u b c)) - 1
          = sizeB r + 1 + (sizeB (B.nd u b c) - 1) := by
        show sizeB r + 1 + sizeB (B.nd u b c) - 1 = _
        omega
      have hIH := iha hAne (d + 1)
      have hT : ent (matB (B.nd v r (.nd u b c)) d) (sizeB r + 1 + (sizeB (B.nd u b c) - 1)) 0
          = ent (matB (B.nd u b c) (d + 1)) (sizeB (B.nd u b c) - 1) 0 :=
        ent_nd_right v r (.nd u b c) d _ 0
      have hTd : d < ent (matB (B.nd u b c) (d + 1)) (sizeB (B.nd u b c) - 1) 0 := by
        have := ent_lb (B.nd u b c) (d + 1) (sizeB (B.nd u b c) - 1) (by omega)
        omega
      have hmapne : ((lastSpine (B.nd u b c)).map (fun i => sizeB r + 1 + i)) ≠ [] := by
        intro hc
        exact lastSpine_ne_nil _ hAne (List.map_eq_nil_iff.mp hc)
      have hsp : ((lastSpine (B.nd v r (.nd u b c))).dropLast).getLast?
          = (sizeB r :: (((lastSpine (B.nd u b c)).dropLast).map
              (fun i => sizeB r + 1 + i))).getLast? := by
        show ((sizeB r :: ((lastSpine (B.nd u b c)).map
            (fun i => sizeB r + 1 + i))).dropLast).getLast? = _
        rw [List.dropLast_cons_of_ne_nil hmapne, ← List.map_dropLast]
      rw [hsz, hsp]
      cases hq : ((lastSpine (B.nd u b c)).dropLast).getLast? with
      | none =>
        have hnil : ((lastSpine (B.nd u b c)).dropLast) = [] := List.getLast?_eq_none_iff.mp hq
        rw [hnil, show (([] : List Nat).map (fun i => sizeB r + 1 + i)) = [] from rfl]
        show _ = some (sizeB r)
        rw [hq] at hIH
        have hmin := min_of_parent0_none _ _ hIH
        refine parent0_eq_some _ _ (sizeB r) (by omega) ?_ ?_
        · rw [hT, ent_nd_node v r (.nd u b c) d 0]
          exact hTd
        · intro p hp1 hp2
          have hi : p - (sizeB r + 1) < sizeB (B.nd u b c) - 1 := by omega
          have hpe : p = sizeB r + 1 + (p - (sizeB r + 1)) := by omega
          rw [hT, hpe, ent_nd_right v r (.nd u b c) d _ 0]
          exact hmin _ hi
      | some q =>
        have hdlne : ((lastSpine (B.nd u b c)).dropLast) ≠ [] := by
          intro hc
          rw [hc] at hq
          exact absurd hq (by simp)
        rw [getLast?_cons_of_ne_nil _ _ (by
          intro hc
          exact hdlne (List.map_eq_nil_iff.mp hc)), List.getLast?_map, hq]
        show _ = some (sizeB r + 1 + q)
        rw [hq] at hIH
        obtain ⟨hqm, hqmax⟩ := List.max?_eq_some_iff.mp hIH
        have hq1 : q < sizeB (B.nd u b c) - 1 :=
          List.mem_range.mp (List.mem_filter.mp hqm).1
        have hq2 : ent (matB (B.nd u b c) (d + 1)) q 0
            < ent (matB (B.nd u b c) (d + 1)) (sizeB (B.nd u b c) - 1) 0 :=
          of_decide_eq_true (List.mem_filter.mp hqm).2
        refine parent0_eq_some _ _ (sizeB r + 1 + q) (by omega) ?_ ?_
        · rw [hT, ent_nd_right v r (.nd u b c) d q 0]
          exact hq2
        · intro p hp1 hp2
          have hi : q < p - (sizeB r + 1) ∧ p - (sizeB r + 1) < sizeB (B.nd u b c) - 1 := by
            omega
          have hpe : p = sizeB r + 1 + (p - (sizeB r + 1)) := by omega
          rw [hT, hpe, ent_nd_right v r (.nd u b c) d _ 0]
          rcases Nat.lt_or_ge (ent (matB (B.nd u b c) (d + 1)) (p - (sizeB r + 1)) 0)
              (ent (matB (B.nd u b c) (d + 1)) (sizeB (B.nd u b c) - 1) 0) with hc | hc
          · exfalso
            have hmem : (p - (sizeB r + 1))
                ∈ (List.range (sizeB (B.nd u b c) - 1)).filter
                    (fun z => decide (ent (matB (B.nd u b c) (d + 1)) z 0
                      < ent (matB (B.nd u b c) (d + 1)) (sizeB (B.nd u b c) - 1) 0)) :=
              List.mem_filter.mpr ⟨List.mem_range.mpr hi.2, decide_eq_true hc⟩
            have := hqmax _ hmem
            omega
          · exact hc

/-- 最後の節の**木の親** (祖先鎖の最後から 2 番目; 無ければ `0`)。 -/
def j0B (t : B) : Nat := (((lastSpine t).dropLast).getLast?).getD 0

/-- 行列の側の `j0`、まだ `Option` のまま。 -/
theorem fpar_last_opt (t : B) (h : t ≠ .nil) :
    fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0
      = (match ((lastSpine t).dropLast).getLast? with
         | none => (-1 : Int)
         | some p => ((p : Nat) : Int)) := by
  have hlen : lenI (psM (matB t 0)) = ((sizeB t : Nat) : Int) := lenI_matB t
  have hpos : 0 < sizeB t := sizeB_pos t h
  rw [fpar_zero, hlen,
    show ((sizeB t : Nat) : Int) - 1 = ((sizeB t - 1 : Nat) : Int) from by omega,
    fpar0_eq_parent (matB t 0) (sizeB t - 1) (by rw [sizeB_matB]; omega),
    parent_lastSpine t h 0]

/-- principal なら最後の節には木の親がある。 -/
theorem lastSpine_dropLast_ne (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) :
    ((lastSpine t).dropLast).getLast? = some (j0B t) := by
  have hne : t ≠ .nil := by
    intro hc
    rw [hc] at h1
    have hz : sizeB (.nil : B) = 0 := rfl
    omega
  have hlen : lenI (psM (matB t 0)) = ((sizeB t : Nat) : Int) := lenI_matB t
  cases hq : ((lastSpine t).dropLast).getLast? with
  | none =>
    exfalso
    have hf : fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0 = -1 := by
      rw [fpar_last_opt t hne, hq]
    have hanc : isAnc (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0 = false := by
      show (if (0 : Int) < 0 ∨ (0 : Int) ≥ lenI (psM (matB t 0)) then false
            else isAncAux ((psM (matB t 0)).length + 1) (psM (matB t 0)) 0
                   (lenI (psM (matB t 0)) - 1) 0) = false
      rw [if_neg (by rw [hlen]; omega)]
      show (if ((0 : Int) == lenI (psM (matB t 0)) - 1) then true
            else if fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0 == -1 then false
                 else isAncAux ((psM (matB t 0)).length) (psM (matB t 0)) 0
                        (fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0) 0) = false
      rw [show ((0 : Int) == lenI (psM (matB t 0)) - 1) = false from by
          rw [hlen]; exact decide_eq_false (by omega)]
      simp only [Bool.false_eq_true, if_false]
      rw [hf, beqI_self]
      rfl
    rw [show isPrincipalP (psM (matB t 0))
        = (!isZeroP (psM (matB t 0)) && isAnc (psM (matB t 0)) 0
            (lenI (psM (matB t 0)) - 1) 0) from rfl, hanc, Bool.and_false] at hprin
    exact Bool.noConfusion hprin
  | some q =>
    have hj : j0B t = q := by
      show ((((lastSpine t).dropLast).getLast?).getD 0) = q
      rw [hq]
      rfl
    rw [hj]

/-- **`j0` は最後の節の木の親。** -/
theorem fpar_last_spine (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) :
    fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0 = ((j0B t : Nat) : Int) := by
  have hne : t ≠ .nil := by
    intro hc
    rw [hc] at h1
    have hz : sizeB (.nil : B) = 0 := rfl
    omega
  rw [fpar_last_opt t hne, lastSpine_dropLast_ne t h1 hprin]

/-- 木の親は最後の列より左。 -/
theorem j0B_lt (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) : j0B t < sizeB t - 1 := by
  have hne : t ≠ .nil := by
    intro hc
    rw [hc] at h1
    have hz : sizeB (.nil : B) = 0 := rfl
    omega
  exact parent0_lt (matB t 0) (sizeB t - 1) (j0B t)
    (by rw [parent_lastSpine t hne 0]; exact lastSpine_dropLast_ne t h1 hprin)

/-! ### 2. `isAdm` は完全に局所的 -/

/-- 前順 `j` 番目の節の深さ (行 0)。 -/
def entD (t : B) (j : Nat) : Nat := ent (matB t 0) j 0
/-- 前順 `j` 番目の節の段 (行 1)。 -/
def entL (t : B) (j : Nat) : Nat := ent (matB t 0) j 1

/-- 深さも段も真に増えるか。 -/
def bothInc (t : B) (j : Nat) : Bool :=
  decide (entD t j < entD t (j + 1)) && decide (entL t j < entL t (j + 1))

/-- **`isAdm` の添字の側の形。** 隣り合う 2 列だけを見る。 -/
def isAdmB (t : B) (j : Nat) : Bool :=
  !((decide (1 ≤ j) && bothInc t (j - 1)) && (decide (j + 1 < sizeB t) && bothInc t j))

/-- §26 の `isParentP_succ_iff` を Bool の等式にしたもの。両端も込み。 -/
theorem isParentP_succ_bool (M : Matrix) (j : Nat) :
    isParentP (psM M) 1 (((j : Nat) : Int) + 1) ((j : Nat) : Int)
      = (decide (ent M j 0 < ent M (j + 1) 0) && decide (ent M j 1 < ent M (j + 1) 1)) := by
  rcases Nat.lt_or_ge (j + 1) M.length with h | h
  · cases hp : isParentP (psM M) 1 (((j : Nat) : Int) + 1) ((j : Nat) : Int) with
    | true =>
      obtain ⟨h0, h1⟩ := (isParentP_succ_iff M j h).mp hp
      rw [decide_eq_true h0, decide_eq_true h1]
      rfl
    | false =>
      refine (Bool.eq_false_iff.mpr (fun hc => ?_)).symm
      have hb := (Bool.and_eq_true _ _).mp hc
      have h2 := (isParentP_succ_iff M j h).mpr
        ⟨of_decide_eq_true hb.1, of_decide_eq_true hb.2⟩
      rw [hp] at h2
      exact Bool.noConfusion h2
  · rw [isParentP_succ_oob M j h, ent_zero_of_ge_len M (j + 1) h,
      show decide (ent M j 0 < 0) = false from decide_eq_false (by omega)]
    rfl

/-- 行列の右端では `bothInc` は自動的に偽。 -/
theorem bothInc_oob (t : B) (j : Nat) (h : sizeB t ≤ j + 1) : bothInc t j = false := by
  have he : ent (matB t 0) (j + 1) 0 = 0 :=
    ent_zero_of_ge_len _ _ (by rw [sizeB_matB]; omega)
  show (decide (entD t j < entD t (j + 1)) && _) = false
  rw [show entD t (j + 1) = 0 from he,
    show decide (entD t j < 0) = false from decide_eq_false (by omega)]
  rfl

/-- **`isAdm` は完全に局所的。** 標準形の仮定は要らない。 -/
theorem isAdm_tree (t : B) (j : Nat) (hj : j ≤ sizeB t) :
    isAdm (psM (matB t 0)) ((j : Nat) : Int) = isAdmB t j := by
  have hlen : lenI (psM (matB t 0)) = ((sizeB t : Nat) : Int) := lenI_matB t
  have hA : isParentP (psM (matB t 0)) 1 (((j : Nat) : Int) + 1) ((j : Nat) : Int)
      = bothInc t j := isParentP_succ_bool (matB t 0) j
  have hA' : (decide (j + 1 < sizeB t) && bothInc t j) = bothInc t j := by
    rcases Nat.lt_or_ge (j + 1) (sizeB t) with h | h
    · rw [decide_eq_true h, Bool.true_and]
    · rw [bothInc_oob t j h, Bool.and_false]
  have hB : isParentP (psM (matB t 0)) 1 ((j : Nat) : Int) (((j : Nat) : Int) - 1)
      = (decide (1 ≤ j) && bothInc t (j - 1)) := by
    cases j with
    | zero =>
      show (decide ((0 : Int) ≤ (0 : Int) - 1) && _ && _) = _
      rw [show decide ((0 : Int) ≤ (0 : Int) - 1) = false from decide_eq_false (by omega)]
      rfl
    | succ k =>
      rw [show (((k + 1 : Nat) : Int)) = ((k : Nat) : Int) + 1 from by omega,
        show ((k : Nat) : Int) + 1 - 1 = ((k : Nat) : Int) from by omega,
        isParentP_succ_bool (matB t 0) k,
        show decide (1 ≤ k + 1) = true from decide_eq_true (by omega), Bool.true_and,
        show k + 1 - 1 = k from by omega]
      rfl
  have hun : isAdm (psM (matB t 0)) ((j : Nat) : Int)
      = (!(decide (((j : Nat) : Int) > lenI (psM (matB t 0)))
          || (isParentP (psM (matB t 0)) 1 ((j : Nat) : Int) (((j : Nat) : Int) - 1)
              && isParentP (psM (matB t 0)) 1 (((j : Nat) : Int) + 1) ((j : Nat) : Int)))) := rfl
  rw [hun, hlen, show decide (((j : Nat) : Int) > ((sizeB t : Nat) : Int)) = false from
      decide_eq_false (by omega), Bool.false_or, hA, hB, ← hA']
  rfl

/-! ### 3. `Adm` の再帰 -/

/-- **`Adm` の添字の側の再帰。** `j` 以下で最大の許された位置。 -/
def admB (t : B) : Nat → Nat
  | 0 => 0
  | k + 1 => if isAdmB t (k + 1) then k + 1 else admB t k

theorem admAux_neg (f : Nat) (M : Trans.Recal.PS) (x : Int) (h : x < 0) :
    admAux f M x = 0 := by
  cases f with
  | zero => rfl
  | succ g =>
    show (if x < 0 then (0 : Int) else if isAdm M x then x else admAux g M (x - 1)) = 0
    rw [if_pos h]

theorem admAux_tree (t : B) : ∀ (f j : Nat), j < f → j ≤ sizeB t →
    admAux f (psM (matB t 0)) ((j : Nat) : Int) = ((admB t j : Nat) : Int) := by
  intro f
  induction f with
  | zero => intro j hj _; omega
  | succ g ih =>
    intro j hj hs
    show (if ((j : Nat) : Int) < 0 then (0 : Int)
          else if isAdm (psM (matB t 0)) ((j : Nat) : Int) then ((j : Nat) : Int)
          else admAux g (psM (matB t 0)) (((j : Nat) : Int) - 1)) = _
    rw [if_neg (by omega), isAdm_tree t j hs]
    cases j with
    | zero =>
      by_cases hz : isAdmB t 0
      · rw [if_pos hz]; rfl
      · rw [if_neg hz, show ((0 : Nat) : Int) - 1 = (-1 : Int) from by omega,
          admAux_neg g _ _ (by omega)]
        rfl
    | succ k =>
      by_cases hz : isAdmB t (k + 1)
      · rw [if_pos hz]
        show _ = ((admB t (k + 1) : Nat) : Int)
        rw [show admB t (k + 1) = if isAdmB t (k + 1) then k + 1 else admB t k from rfl,
          if_pos hz]
      · rw [if_neg hz,
          show (((k + 1 : Nat) : Int) - 1) = ((k : Nat) : Int) from by omega,
          ih k (by omega) (by omega)]
        show _ = ((admB t (k + 1) : Nat) : Int)
        rw [show admB t (k + 1) = if isAdmB t (k + 1) then k + 1 else admB t k from rfl,
          if_neg hz]

/-- **`Adm` は添字の側の再帰。** -/
theorem adm_tree (t : B) (j : Nat) (hj : j ≤ sizeB t) :
    adm (psM (matB t 0)) ((j : Nat) : Int) = ((admB t j : Nat) : Int) := by
  show admAux ((psM (matB t 0)).length + 2) (psM (matB t 0)) ((j : Nat) : Int) = _
  refine admAux_tree t _ j ?_ hj
  rw [psM_len, sizeB_matB]
  omega

/-! ### 4. 型 -/

/-- **`transTypeMain` の添字の側の形。** -/
def tyMainB (t : B) (j0 j1 : Nat) : Nat :=
  if entL t j1 == 0 then (if isAdmB t j0 then 1 else 2)
  else if entL t j1 ≤ entL t j0 then (if isAdmB t j0 then 3 else 4)
  else if j0 + 1 < j1 then 5 else 6

theorem beqI_nat_zero (n : Nat) : (((n : Nat) : Int) == (0 : Int)) = (n == 0) := by
  cases n with
  | zero => rfl
  | succ k =>
    rw [show ((((k + 1 : Nat) : Int)) == (0 : Int)) = false from decide_eq_false (by omega)]
    rfl

/-- **`transTypeMain` を木の言葉で。** -/
theorem transTypeMain_tree (t : B) (j0 j1 : Nat) (h0 : j0 ≤ sizeB t) :
    transTypeMain (psM (matB t 0)) ((j0 : Nat) : Int) ((j1 : Nat) : Int)
      = tyMainB t j0 j1 := by
  have g0 : gp1 (psM (matB t 0)) ((j0 : Nat) : Int) = ((entL t j0 : Nat) : Int) :=
    psM_gp1 (matB t 0) j0
  have g1 : gp1 (psM (matB t 0)) ((j1 : Nat) : Int) = ((entL t j1 : Nat) : Int) :=
    psM_gp1 (matB t 0) j1
  show (if gp1 (psM (matB t 0)) ((j1 : Nat) : Int) == 0 then
          (if isAdm (psM (matB t 0)) ((j0 : Nat) : Int) then 1 else 2)
        else if gp1 (psM (matB t 0)) ((j0 : Nat) : Int)
            ≥ gp1 (psM (matB t 0)) ((j1 : Nat) : Int) then
          (if isAdm (psM (matB t 0)) ((j0 : Nat) : Int) then 3 else 4)
        else if ((j0 : Nat) : Int) + 1 < ((j1 : Nat) : Int) then 5 else 6) = _
  rw [g0, g1, beqI_nat_zero, isAdm_tree t j0 h0]
  show (if (entL t j1 == 0) = true then (if isAdmB t j0 = true then 1 else 2)
        else if ((entL t j0 : Nat) : Int) ≥ ((entL t j1 : Nat) : Int)
             then (if isAdmB t j0 = true then 3 else 4)
             else if ((j0 : Nat) : Int) + 1 < ((j1 : Nat) : Int) then 5 else 6)
    = (if (entL t j1 == 0) = true then (if isAdmB t j0 = true then 1 else 2)
       else if entL t j1 ≤ entL t j0 then (if isAdmB t j0 = true then 3 else 4)
       else if j0 + 1 < j1 then 5 else 6)
  by_cases hz : (entL t j1 == 0) = true
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    by_cases hle : entL t j1 ≤ entL t j0
    · rw [if_pos (show ((entL t j0 : Nat) : Int) ≥ ((entL t j1 : Nat) : Int) from by omega),
        if_pos hle]
    · rw [if_neg (show ¬(((entL t j0 : Nat) : Int) ≥ ((entL t j1 : Nat) : Int)) from by omega),
        if_neg hle]
      by_cases hlt : j0 + 1 < j1
      · rw [if_pos (show ((j0 : Nat) : Int) + 1 < ((j1 : Nat) : Int) from by omega), if_pos hlt]
      · rw [if_neg (show ¬(((j0 : Nat) : Int) + 1 < ((j1 : Nat) : Int)) from by omega),
          if_neg hlt]

/-! ### 枝の 4 つの材料、まとめて -/

theorem lenI_sub_one (t : B) (h1 : 1 < sizeB t) :
    lenI (psM (matB t 0)) - 1 = ((sizeB t - 1 : Nat) : Int) := by
  rw [lenI_matB]
  omega

/-- **枝が使う `ty`。** -/
theorem branch_ty (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) :
    transTypeMain (psM (matB t 0))
        (fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0)
        (lenI (psM (matB t 0)) - 1)
      = tyMainB t (j0B t) (sizeB t - 1) := by
  rw [fpar_last_spine t h1 hprin, lenI_sub_one t h1]
  exact transTypeMain_tree t (j0B t) (sizeB t - 1) (by
    have := j0B_lt t h1 hprin
    omega)

/-- **枝が要求する `jn1`。** -/
theorem branch_jn1 (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) :
    adm (psM (matB t 0)) (fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0)
      = ((admB t (j0B t) : Nat) : Int) := by
  rw [fpar_last_spine t h1 hprin]
  exact adm_tree t (j0B t) (by
    have := j0B_lt t h1 hprin
    omega)

/-! ### 5. memo に外れた型 1-6 の枝 -/

/-- `c1` を計算し終えた時点の (値, 表)。 -/
def mainC1 (f : Nat) (M : Trans.Recal.PS) (tbl : Trans.Recal.Memo) : BT × Trans.Recal.Memo :=
  (Trans.Recal.runAux f (predP M) (some (adm M (fpar M 0 (lenI M - 1) 0)))).run
    ((Trans.Recal.runAux f (predP M) none).run tbl).2

/-- 枝の `c2`。 -/
def mainC2 (M : Trans.Recal.PS) (c1 : BT) : BT :=
  mkC2 M (fpar M 0 (lenI M - 1) 0) (lenI M - 1)
    (transTypeMain M (fpar M 0 (lenI M - 1) 0) (lenI M - 1)) c1

/-- `replMark` に渡す深さの上限。 -/
def mainDep (c1 c2 : BT) : Nat :=
  Trans.Dict.BT.size c1 + Trans.Dict.BT.size c2 + 4

/-- 型 1-6 の枝が `Trans` に返す値。 -/
def mainVal (M : Trans.Recal.PS) (t1 c1 : BT) : BT :=
  (replMark (Trans.Dict.BT.size t1 + mainDep c1 (mainC2 M c1)) t1 c1 (mainC2 M c1)).getD BT.zero

/-- `c0` を計算し終えた時点の (値, 表)。 -/
def mainC0 (f : Nat) (M : Trans.Recal.PS) (m : Int) (tbl : Trans.Recal.Memo) :
    BT × Trans.Recal.Memo :=
  (Trans.Recal.runAux f (predP M) (some m)).run (mainC1 f M tbl).2

/-- 型 1-6 の枝が `Mark m` (`m < j1`) に返す値。 -/
def markVal (M : Trans.Recal.PS) (c0 c1 : BT) : BT :=
  if isMarkedB c0 c1 then
    (replMark (Trans.Dict.BT.size c0 + mainDep c1 (mainC2 M c1)) c0 c1 (mainC2 M c1)).getD BT.zero
  else BT.D (gp1 M (lenI M - 1)).toNat BT.zero

/-- memo に外れた型 1-6 の枝 (要求は `Trans`)。 -/
theorem run_main_miss_none (f : Nat) (M : Trans.Recal.PS) (tbl : Trans.Recal.Memo) (t1 : BT)
    (hred : isReducedP M = true) (hj1 : (lenI M - 1 == 0) = false)
    (hprin : isPrincipalP M = true)
    (ht1 : ((Trans.Recal.runAux f (predP M) none).run tbl).1 = t1)
    (hne : (t1 == BT.zero) = false)
    (h : tbl.find? (fun q => q.1 == (M, (none : Option Int))) = none) :
    (Trans.Recal.runAux (f + 1) M none).run tbl
      = (mainVal M t1 (mainC1 f M tbl).1,
         ((M, (none : Option Int)), mainVal M t1 (mainC1 f M tbl).1) :: (mainC1 f M tbl).2) := by
  have hz' : Trans.Recal.runAux f (predP M) none tbl
      = (t1, (Trans.Recal.runAux f (predP M) none tbl).2) := by
    rw [← ht1]
    rfl
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, pure,
    get, getThe, MonadStateOf.get, h, hred, hj1, hprin,
    Bool.not_true, Bool.false_eq_true, if_false]
  rw [hz']
  simp only [hne, Bool.false_eq_true, if_false]
  rfl

/-- memo に外れた型 1-6 の枝 (要求は `Mark m`、`m < j1`)。 -/
theorem run_main_miss_mark_lt (f : Nat) (M : Trans.Recal.PS) (m : Int)
    (tbl : Trans.Recal.Memo) (t1 : BT)
    (hred : isReducedP M = true) (hj1 : (lenI M - 1 == 0) = false)
    (hprin : isPrincipalP M = true)
    (ht1 : ((Trans.Recal.runAux f (predP M) none).run tbl).1 = t1)
    (hne : (t1 == BT.zero) = false) (hm : m < lenI M - 1)
    (h : tbl.find? (fun q => q.1 == (M, (some m : Option Int))) = none) :
    (Trans.Recal.runAux (f + 1) M (some m)).run tbl
      = (markVal M (mainC0 f M m tbl).1 (mainC1 f M tbl).1,
         ((M, (some m : Option Int)),
            markVal M (mainC0 f M m tbl).1 (mainC1 f M tbl).1) :: (mainC0 f M m tbl).2) := by
  have hz' : Trans.Recal.runAux f (predP M) none tbl
      = (t1, (Trans.Recal.runAux f (predP M) none tbl).2) := by
    rw [← ht1]
    rfl
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, pure,
    get, getThe, MonadStateOf.get, h, hred, hj1, hprin,
    Bool.not_true, Bool.false_eq_true, if_false]
  rw [hz']
  simp only [hne, Bool.false_eq_true, if_false, if_pos hm]
  rfl

/-- memo に外れた型 1-6 の枝 (要求は `Mark m`、`j1 ≤ m`)。 -/
theorem run_main_miss_mark_ge (f : Nat) (M : Trans.Recal.PS) (m : Int)
    (tbl : Trans.Recal.Memo) (t1 : BT)
    (hred : isReducedP M = true) (hj1 : (lenI M - 1 == 0) = false)
    (hprin : isPrincipalP M = true)
    (ht1 : ((Trans.Recal.runAux f (predP M) none).run tbl).1 = t1)
    (hne : (t1 == BT.zero) = false) (hm : ¬(m < lenI M - 1))
    (h : tbl.find? (fun q => q.1 == (M, (some m : Option Int))) = none) :
    (Trans.Recal.runAux (f + 1) M (some m)).run tbl
      = (BT.D (gp1 M (lenI M - 1)).toNat BT.zero,
         ((M, (some m : Option Int)), BT.D (gp1 M (lenI M - 1)).toNat BT.zero)
           :: (mainC1 f M tbl).2) := by
  have hz' : Trans.Recal.runAux f (predP M) none tbl
      = (t1, (Trans.Recal.runAux f (predP M) none tbl).2) := by
    rw [← ht1]
    rfl
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, pure,
    get, getThe, MonadStateOf.get, h, hred, hj1, hprin,
    Bool.not_true, Bool.false_eq_true, if_false]
  rw [hz']
  simp only [hne, Bool.false_eq_true, if_false, if_neg hm]
  rfl

/-! ### 測定 -/

/-- 型 1-6 の枝に落ちる標準形の添字。 -/
def pop6 (L n : Nat) : List B :=
  (popNFB L n).filter fun t =>
    1 < sizeB t && isPrincipalP (psM (matB t 0)) && !(bVal (dropLastB t) == BT.zero)

-- 母集団の大きさ。
#guard (pop6 3 6).length == 440
-- 1. `j0` は祖先鎖の最後から 2 番目 (証明ずみ、記録として)。
#guard (pop6 3 6).all fun t =>
  let M := psM (matB t 0)
  fpar M 0 (lenI M - 1) 0 == ((j0B t : Nat) : Int)
-- 2. `isAdm` は局所的 (証明ずみ、全位置で)。
#guard (pop6 3 6).all fun t =>
  (List.range (sizeB t + 1)).all fun j => isAdm (psM (matB t 0)) ((j : Nat) : Int) == isAdmB t j
-- 3. `Adm` は添字の側の再帰 (証明ずみ、全位置で)。
#guard (pop6 3 6).all fun t =>
  (List.range (sizeB t + 1)).all fun j =>
    adm (psM (matB t 0)) ((j : Nat) : Int) == ((admB t j : Nat) : Int)
-- 4. 型は木の言葉で読める (証明ずみ)。
#guard (pop6 3 6).all fun t =>
  let M := psM (matB t 0)
  transTypeMain M (fpar M 0 (lenI M - 1) 0) (lenI M - 1) == tyMainB t (j0B t) (sizeB t - 1)
-- 型の分布 (440 個): 1:176, 2:8, 3:76, 4:8, 5:116, 6:56。
#guard ((pop6 3 6).map fun t => tyMainB t (j0B t) (sizeB t - 1)).foldl
    (fun (a : List (Nat × Nat)) k =>
      if a.any (fun p => p.1 == k) then a.map (fun p => if p.1 == k then (p.1, p.2 + 1) else p)
      else a ++ [(k, 1)]) []
  == [(1, 176), (6, 56), (3, 76), (5, 116), (2, 8), (4, 8)]

-- 2 は標準形を仮定しない: 標準形でない添字でも成り立つ。
#guard (((List.range 5).flatMap (enumNodes 3)).filter fun t => t != .nil).length == 1290
#guard (((List.range 5).flatMap (enumNodes 3)).filter fun t => t != .nil).all fun t =>
  (List.range (sizeB t + 1)).all fun j => isAdm (psM (matB t 0)) ((j : Nat) : Int) == isAdmB t j

-- **まだ証明していないこと**: `replMark` の等式。次の節の仕事。
#guard (pop6 3 6).all fun t =>
  let s := dropLastB t
  let M := psM (matB t 0)
  let c1 := bMark s (admB t (j0B t))
  let c2 := mainC2 M c1
  let t1 := bVal s
  markOKB s (admB t (j0B t))
    && ((replMark (Trans.Dict.BT.size t1 + mainDep c1 c2) t1 c1 c2).getD BT.zero == bVal t)
-- 465 個 (段 < 4) でも同じ。
#guard (pop6 4 6).length == 465
#guard (pop6 4 6).all fun t =>
  let s := dropLastB t
  let M := psM (matB t 0)
  let c1 := bMark s (admB t (j0B t))
  let c2 := mainC2 M c1
  let t1 := bVal s
  markOKB s (admB t (j0B t))
    && ((replMark (Trans.Dict.BT.size t1 + mainDep c1 c2) t1 c1 c2).getD BT.zero == bVal t)
-- Mark の側も同じ 440 個で。
#guard (pop6 3 6).all fun t =>
  let s := dropLastB t
  let M := psM (matB t 0)
  let c1 := bMark s (admB t (j0B t))
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m)
      || (if ((m : Nat) : Int) < lenI M - 1
          then markOKB s m && (markVal M (bMark s m) c1 == bMark t m)
          else BT.D (gp1 M (lenI M - 1)).toNat BT.zero == bMark t m)

end

/-! ## §58 THE SUBSTITUTION LEMMA

    subst_bVal      replMark N (bVal s) (bMark s m) (bMark t m) = some (bVal t)
    subst_bMark     the same one level in: inside the contribution of an ancestor m0 ≤ m
    subst_K         the single-node version both of them are assembled from
    subst_PQ        the induction — `bArg` and `bClose (bFold ...)` proved together
    isMarkedB_bVal / isMarkedB_bMark   and therefore the mark IS on the rightmost spine

§57 named the four inputs of the types 1-6 branch on the index side and left open the one
equation with mathematical content: `bMark s jn1` occurs on the rightmost spine of `bVal s`,
and replacing it by the `t`-side contribution gives `bVal t`.  This section proves it, in the
general form the measurement found — no `j0`, no `adm`, no `ty` anywhere:

    s = dropLastB t,   m any position with `markOKB s m` and `markOKB t m`,
    fuel N at least `size (bVal s) + 1`  (so §57's measured `... + 4` bound is more than enough;
    `subst_bVal'` is that spelling).

WHY IT IS TRUE.  `bVal s` and `bVal t` are the SAME CONTEXT around node `m`'s contribution:
appending a node in preorder changes what `m` contributes — the new node lands inside `m`'s
subtree — and leaves everything outside `m` untouched.  `markOKB` is what makes that difference
a subterm `replMark` can reach: `m` is on `lastSpine`, which is the rightmost spine `replMark`
walks, and its contribution is a single `D`, hence one COMPONENT of a sum and not a sum itself.

WHAT CARRIES IT.  Three things.

  * `SubL ls lt cs ct` states the claim about the COMPONENT LISTS, with an arbitrary atom prefix
    `pre` in front.  `bplus a b` is `ofL (a.toL ++ b.toL)`, so "descend into the last summand"
    is `pre := pre ++ a.toL` — an append, with nothing to reassemble afterwards.  That is what
    lets ONE induction serve `bArg` (a sum of contributions), `bFold`'s accumulator (a sum whose
    last atom hides another sum) and `bVal` (a sum with a special first node).

  * `msz`, the number of `D`s in a term, additive over `bplus`.  `replMark` compares the term it
    stands on with `c` BEFORE descending, so it must not match early.  `msz_markIn` says a
    node's contribution weighs no more than the value it sits in, so every term strictly above
    the hole is strictly heavier than `c` and the test fails.  Weight is all the "the mark is a
    proper subterm" this proof needs.

  * `bK`, §48's three-way contribution as a function of its own.  `bArg`, `bFold` and `markIn`
    all call it, so the base case (the hole IS this node) and the step (the hole is inside this
    node's children) are proved once, in `subst_K_aux`, and both halves of the induction quote
    them.

§48's collapse rule is exactly why `subst_PQ` proves TWO statements at once: an ancestor of `m`
may be collapsed, and then the context around the hole is not a chain of `D`s but `bFold`'s
accumulator pair.  `bClose`'s three shapes are the second half.

The fuel bound is `size (current term) + 1` all the way down — each `replMark` step moves to a
strictly smaller subterm, so the bound is preserved and no separate depth measure is needed.

`nfB` is used ONCE, and only for `bVal`: it forces every top-level node to level 0, so the
collapse rule cannot fire at the top and `bVal`'s summand agrees with `markIn`'s.  Everything
below the top — `subst_PQ`, `subst_K`, `subst_bMark` — needs no normal form at all, and that is
measured on the UNFILTERED enumeration as well.

WHAT IS NOT CLAIMED.  `subst_bMark` assumes `m0 ≤ m`: the outer mark is an ANCESTOR of the hole.
§57's `markVal` tests `isMarkedB c0 c1` instead, and the two are not equivalent — 26 positions
of `popNFB 3 6` have `m < m0` (outer mark a DESCENDANT) and `isMarkedB` true all the same,
because the two contributions happen to be the same term (guard 7 below).  The equation still
measures true there, but proving it needs "equal marks in `s` give equal marks in `t`", a
statement about the value functions rather than about `replMark`.  What IS proved is the
direction §59 needs to discharge the test: `isMarkedB_bMark`, the test succeeds whenever
`m0 ≤ m`.  Nothing here evaluates `runAux`; the glue to §57's branch data is §59's job. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### 0. 項の等号 -/

theorem bt_beq_true : ∀ (x y : BT), (x == y) = true → x = y := by
  intro x
  induction x with
  | zero =>
    intro y h
    cases y with
    | zero => rfl
    | D u a => exact Bool.noConfusion h
    | sum a b => exact Bool.noConfusion h
  | D u a ih =>
    intro y h
    cases y with
    | zero => exact Bool.noConfusion h
    | D v b =>
      have h2 : ((u == v) && (a == b)) = true := h
      have hb := (Bool.and_eq_true _ _).mp h2
      rw [show u = v from of_decide_eq_true hb.1, ih b hb.2]
    | sum a b => exact Bool.noConfusion h
  | sum p q ihp ihq =>
    intro y h
    cases y with
    | zero => exact Bool.noConfusion h
    | D v b => exact Bool.noConfusion h
    | sum a b =>
      have h2 : ((p == a) && (q == b)) = true := h
      have hb := (Bool.and_eq_true _ _).mp h2
      rw [ihp a hb.1, ihq b hb.2]

theorem bt_beq_refl : ∀ (x : BT), (x == x) = true := by
  intro x
  induction x with
  | zero => rfl
  | D u a ih =>
    show ((u == u) && (a == a)) = true
    rw [show (u == u) = true from beq_self_eq_true u, ih]
    rfl
  | sum p q ihp ihq =>
    show ((p == p) && (q == q)) = true
    rw [ihp, ihq]
    rfl

theorem bt_beq_false (x y : BT) (h : ¬ (x = y)) : (x == y) = false := by
  cases hb : (x == y) with
  | true => exact absurd (bt_beq_true x y hb) h
  | false => rfl

/-! ### 1. 和の重み -/

/-- 成分の重み。`bplus` について加法的な大きさ。 -/
def msz : BT → Nat
  | .zero => 0
  | .D _ a => 1 + msz a
  | .sum a b => msz a + msz b

/-- 成分の並びの重み。 -/
def mszL : List BT → Nat
  | [] => 0
  | x :: r => msz x + mszL r

theorem mszL_append : ∀ (l1 l2 : List BT), mszL (l1 ++ l2) = mszL l1 + mszL l2
  | [], l2 => by show mszL l2 = 0 + mszL l2; omega
  | x :: r, l2 => by
      show msz x + mszL (r ++ l2) = (msz x + mszL r) + mszL l2
      rw [mszL_append r l2]
      omega

theorem msz_ofL : ∀ (l : List BT), msz (BT.ofL l) = mszL l
  | [] => rfl
  | [a] => by show msz a = msz a + 0; omega
  | a :: b :: r => by
      show msz a + msz (BT.ofL (b :: r)) = msz a + mszL (b :: r)
      rw [msz_ofL (b :: r)]

theorem msz_toL : ∀ (t : BT), mszL t.toL = msz t
  | .zero => rfl
  | .D u a => by show msz (BT.D u a) + 0 = msz (BT.D u a); omega
  | .sum a b => by
      show mszL (a.toL ++ b.toL) = msz a + msz b
      rw [mszL_append, msz_toL a, msz_toL b]

theorem msz_bplus (a b : BT) : msz (bplus a b) = msz a + msz b := by
  show msz (BT.ofL (a.toL ++ b.toL)) = _
  rw [msz_ofL, mszL_append, msz_toL, msz_toL]

/-! ### 2. 大きさ (燃料の目安) -/

theorem size_pos : ∀ (t : BT), 1 ≤ BT.size t
  | .zero => Nat.le_refl 1
  | .D _ a => by show 1 ≤ 1 + BT.size a; omega
  | .sum a b => by show 1 ≤ 1 + BT.size a + BT.size b; omega

theorem size_ofL_last : ∀ (l : List BT) (x : BT), l ≠ [] →
    BT.size x + 1 ≤ BT.size (BT.ofL (l ++ [x]))
  | [], _, h => absurd rfl h
  | [a], x, _ => by
      show BT.size x + 1 ≤ 1 + BT.size a + BT.size x
      omega
  | a :: b :: r, x, _ => by
      have ih := size_ofL_last (b :: r) x (List.cons_ne_nil b r)
      show BT.size x + 1 ≤ 1 + BT.size a + BT.size (BT.ofL ((b :: r) ++ [x]))
      omega

/-! ### 3. 成分の並び -/

/-- 並びの成分がすべて `D` であること (`AtomsL` の並び版)。 -/
def Atoms (l : List BT) : Prop := ∀ z ∈ l, ∃ p a, z = BT.D p a

theorem atoms_append (l1 l2 : List BT) (h1 : Atoms l1) (h2 : Atoms l2) : Atoms (l1 ++ l2) := by
  intro z hz
  rcases List.mem_append.mp hz with h | h
  · exact h1 z h
  · exact h2 z h

theorem atoms_single (p : Nat) (a : BT) : Atoms [BT.D p a] := by
  intro z hz
  rw [List.mem_singleton.mp hz]
  exact ⟨p, a, rfl⟩

theorem atoms_toL (t : BT) (h : AtomsL t) : Atoms t.toL := h

/-! ### 4. 節の寄与 `bK` と、定義の展開 -/

/-- **§48 の三分岐**。段 `w` の親の下にある、段 `u`・左兄弟 `r`・子 `c` の節の寄与。 -/
def bK (w u : Nat) (r c : B) : BT :=
  if c == .nil then .D u .zero
  else if u ≤ w || !(r == .nil) || headLvl c ≤ u then .D u (bArg u c)
  else bClose u (bFold u c)

theorem bArg_nd (w u : Nat) (r c : B) : bArg w (.nd u r c) = bplus (bArg w r) (bK w u r c) := rfl

theorem msz_D (w : Nat) (a : BT) : msz (.D w a) = 1 + msz a := rfl

theorem atomsL_bK (w u : Nat) (r c : B) : AtomsL (bK w u r c) := by
  show AtomsL (if c == .nil then (.D u .zero : BT)
    else if u ≤ w || !(r == .nil) || headLvl c ≤ u then .D u (bArg u c)
    else bClose u (bFold u c))
  by_cases h1 : c == .nil
  · rw [if_pos h1]; exact atomsL_D u .zero
  · rw [if_neg h1]
    by_cases h2 : u ≤ w || !(r == .nil) || headLvl c ≤ u
    · rw [if_pos h2]; exact atomsL_D u (bArg u c)
    · rw [if_neg h2]; exact atomsL_bClose u (bFold u c) (atomsL_bArg_bFold c u).2

theorem nfSum_bArg : ∀ (w : Nat) (x : B), NfSum (bArg w x)
  | _, .nil => nfSum_zero
  | w, .nd u r c => by
      show NfSum (bplus (bArg w r) (bK w u r c))
      exact nfSum_bplus _ _ (atomsL_bArg_bFold r w).1 (atomsL_bK w u r c)

theorem bClose_none' (w : Nat) (st : BT × Option BT) (h : st.2 = none) : bClose w st = st.1 := by
  show (match st.2 with | none => st.1 | some a => bplus st.1 (.D w a)) = st.1
  rw [h]

theorem bClose_some' (w : Nat) (st : BT × Option BT) (a : BT) (h : st.2 = some a) :
    bClose w st = bplus st.1 (.D w a) := by
  show (match st.2 with | none => st.1 | some a => bplus st.1 (.D w a)) = _
  rw [h]

theorem bFold_nd_lt (w u : Nat) (r c : B) (h : w < u) :
    bFold w (.nd u r c) = (bplus (bClose w (bFold w r)) (bK w u r c), none) := by
  show (if w < u then (bplus (bClose w (bFold w r)) (bK w u r c), none)
        else match (bFold w r).2 with
             | none => ((bFold w r).1, some (bplus (bFold w r).1 (bK w u r c)))
             | some a => ((bFold w r).1, some (bplus a (bK w u r c)))) = _
  rw [if_pos h]

theorem bFold_nd_ge (w u : Nat) (r c : B) (h : ¬ (w < u)) :
    bFold w (.nd u r c)
      = (match (bFold w r).2 with
         | none => ((bFold w r).1, some (bplus (bFold w r).1 (bK w u r c)))
         | some a => ((bFold w r).1, some (bplus a (bK w u r c)))) := by
  show (if w < u then (bplus (bClose w (bFold w r)) (bK w u r c), none)
        else match (bFold w r).2 with
             | none => ((bFold w r).1, some (bplus (bFold w r).1 (bK w u r c)))
             | some a => ((bFold w r).1, some (bplus a (bK w u r c)))) = _
  rw [if_neg h]

theorem bClose_bFold_nd_lt (w u : Nat) (r c : B) (h : w < u) :
    bClose w (bFold w (.nd u r c)) = bplus (bClose w (bFold w r)) (bK w u r c) := by
  rw [bFold_nd_lt w u r c h]
  exact bClose_none' w _ rfl

theorem bClose_bFold_nd_none (w u : Nat) (r c : B) (h : ¬ (w < u)) (h2 : (bFold w r).2 = none) :
    bClose w (bFold w (.nd u r c))
      = bplus (bFold w r).1 (.D w (bplus (bFold w r).1 (bK w u r c))) := by
  rw [bFold_nd_ge w u r c h, h2]
  exact bClose_some' w _ _ rfl

theorem bClose_bFold_nd_some (w u : Nat) (r c : B) (h : ¬ (w < u)) (a : BT)
    (h2 : (bFold w r).2 = some a) :
    bClose w (bFold w (.nd u r c)) = bplus (bFold w r).1 (.D w (bplus a (bK w u r c))) := by
  rw [bFold_nd_ge w u r c h, h2]
  exact bClose_some' w _ _ rfl

/-! ### 5. 添字の側の道具 -/

theorem lastSpine_nd (u : Nat) (r c : B) :
    lastSpine (.nd u r c) = sizeB r :: (lastSpine c).map (fun i => sizeB r + 1 + i) := rfl

theorem lastSpine_lt : ∀ (x : B) (i : Nat), i ∈ lastSpine x → i < sizeB x := by
  intro x
  induction x with
  | nil =>
    intro i h
    have h' : i ∈ ([] : List Nat) := h
    cases h'
  | nd u r c _ ihc =>
    intro i h
    rw [lastSpine_nd] at h
    rcases List.mem_cons.mp h with he | hm
    · show i < sizeB r + 1 + sizeB c
      omega
    · obtain ⟨j, hj, hje⟩ := List.mem_map.mp hm
      have := ihc j hj
      show i < sizeB r + 1 + sizeB c
      omega

theorem markIn_node (w u : Nat) (r c : B) :
    markIn w (.nd u r c) (sizeB r) = some (bK w u r c) := by
  show (if sizeB r < sizeB r then markIn w r (sizeB r)
        else if (sizeB r == sizeB r) = true then some (bK w u r c)
        else markIn u c (sizeB r - sizeB r - 1)) = some (bK w u r c)
  rw [if_neg (Nat.lt_irrefl (sizeB r)), if_pos (beq_self_eq_true (sizeB r))]

theorem markIn_deep (w u : Nat) (r c : B) (i : Nat) :
    markIn w (.nd u r c) (sizeB r + 1 + i) = markIn u c i := by
  show (if sizeB r + 1 + i < sizeB r then markIn w r (sizeB r + 1 + i)
        else if ((sizeB r + 1 + i) == sizeB r) = true then some (bK w u r c)
        else markIn u c (sizeB r + 1 + i - sizeB r - 1)) = markIn u c i
  rw [if_neg (by omega),
    if_neg (show ¬ (((sizeB r + 1 + i) == sizeB r) = true) from by
      intro hc; exact absurd (eq_of_beq hc) (by omega)),
    show sizeB r + 1 + i - sizeB r - 1 = i from by omega]

theorem markIn_left (w u : Nat) (r c : B) (i : Nat) (h : i < sizeB r) :
    markIn w (.nd u r c) i = markIn w r i := by
  show (if i < sizeB r then markIn w r i
        else if (i == sizeB r) = true then some (bK w u r c)
        else markIn u c (i - sizeB r - 1)) = markIn w r i
  rw [if_pos h]

theorem markIn_oob : ∀ (x : B) (w i : Nat), sizeB x ≤ i → markIn w x i = none := by
  intro x
  induction x with
  | nil => intro w i _; rfl
  | nd u r c _ ihc =>
    intro w i h
    have h' : sizeB r + 1 + sizeB c ≤ i := h
    show (if i < sizeB r then markIn w r i
          else if (i == sizeB r) = true then some (bK w u r c)
          else markIn u c (i - sizeB r - 1)) = none
    rw [if_neg (by omega),
      if_neg (show ¬ ((i == sizeB r) = true) from by
        intro hc; exact absurd (eq_of_beq hc) (by omega))]
    exact ihc u (i - sizeB r - 1) (by omega)

theorem headLvl_dropLast : ∀ (z : B), dropLastB z ≠ .nil → headLvl (dropLastB z) = headLvl z := by
  intro z
  cases z with
  | nil => intro h; exact absurd rfl h
  | nd v r a =>
    cases a with
    | nil =>
      intro h
      have hr : r ≠ .nil := h
      cases r with
      | nil => exact absurd rfl hr
      | nd v2 r2 a2 => rfl
    | nd u b c =>
      intro _
      cases r with
      | nil => rfl
      | nd v2 r2 a2 => rfl

/-! ### 6. 印の重みは、値の重みを超えない -/

theorem msz_bArg_nd_K (w u : Nat) (r c : B) : msz (bK w u r c) ≤ msz (bArg w (.nd u r c)) := by
  rw [bArg_nd, msz_bplus]
  omega

theorem msz_bArg_nd_r (w u : Nat) (r c : B) : msz (bArg w r) ≤ msz (bArg w (.nd u r c)) := by
  rw [bArg_nd, msz_bplus]
  omega

theorem msz_bClose_nd_K (w u : Nat) (r c : B) :
    msz (bK w u r c) ≤ msz (bClose w (bFold w (.nd u r c))) := by
  by_cases hw : w < u
  · rw [bClose_bFold_nd_lt w u r c hw, msz_bplus]
    omega
  · cases hst : (bFold w r).2 with
    | none =>
      rw [bClose_bFold_nd_none w u r c hw hst, msz_bplus, msz_D, msz_bplus]
      omega
    | some a =>
      rw [bClose_bFold_nd_some w u r c hw a hst, msz_bplus, msz_D, msz_bplus]
      omega

theorem msz_bClose_nd_r (w u : Nat) (r c : B) :
    msz (bClose w (bFold w r)) ≤ msz (bClose w (bFold w (.nd u r c))) := by
  by_cases hw : w < u
  · rw [bClose_bFold_nd_lt w u r c hw, msz_bplus]
    omega
  · cases hst : (bFold w r).2 with
    | none =>
      rw [bClose_bFold_nd_none w u r c hw hst, msz_bplus, msz_D, msz_bplus,
        bClose_none' w (bFold w r) hst]
      omega
    | some a =>
      rw [bClose_bFold_nd_some w u r c hw a hst, msz_bplus, msz_D, msz_bplus,
        bClose_some' w (bFold w r) a hst, msz_bplus, msz_D]
      omega

theorem msz_bK_ge (w u : Nat) (r c : B) (K : BT) (j : Nat) (h : markIn u c j = some K)
    (h1 : msz K ≤ msz (bArg u c)) (h2 : msz K ≤ msz (bClose u (bFold u c))) :
    msz K ≤ msz (bK w u r c) := by
  have hcn : ¬ ((c == .nil) = true) := by
    intro hc
    have hnone : markIn u (.nil : B) j = none := rfl
    rw [of_decide_eq_true hc, hnone] at h
    exact absurd h.symm (Option.some_ne_none K)
  show msz K ≤ msz (if c == .nil then (.D u .zero : BT)
    else if u ≤ w || !(r == .nil) || headLvl c ≤ u then .D u (bArg u c)
    else bClose u (bFold u c))
  rw [if_neg hcn]
  by_cases ht : u ≤ w || !(r == .nil) || headLvl c ≤ u
  · rw [if_pos ht, msz_D]
    omega
  · rw [if_neg ht]
    exact h2

/-- **印の重みは値の重み以下。** 節 `i` の寄与は、それを含む値の中の部分項。 -/
theorem msz_markIn : ∀ (x : B) (w i : Nat) (K : BT), markIn w x i = some K →
    msz K ≤ msz (bArg w x) ∧ msz K ≤ msz (bClose w (bFold w x)) := by
  intro x
  induction x with
  | nil =>
    intro w i K h
    have h' : (none : Option BT) = some K := h
    exact absurd h'.symm (Option.some_ne_none K)
  | nd u r c ihr ihc =>
    intro w i K h
    rcases Nat.lt_or_ge i (sizeB r) with hlt | hge
    · rw [markIn_left w u r c i hlt] at h
      obtain ⟨h1, h2⟩ := ihr w i K h
      exact ⟨Nat.le_trans h1 (msz_bArg_nd_r w u r c),
        Nat.le_trans h2 (msz_bClose_nd_r w u r c)⟩
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · rw [← heq, markIn_node w u r c] at h
        rw [← Option.some.inj h]
        exact ⟨msz_bArg_nd_K w u r c, msz_bClose_nd_K w u r c⟩
      · rw [show i = sizeB r + 1 + (i - sizeB r - 1) from by omega, markIn_deep] at h
        obtain ⟨h1, h2⟩ := ihc u (i - sizeB r - 1) K h
        have hK := msz_bK_ge w u r c K (i - sizeB r - 1) h h1 h2
        exact ⟨Nat.le_trans hK (msz_bArg_nd_K w u r c),
          Nat.le_trans hK (msz_bClose_nd_K w u r c)⟩

/-! ### 7. `replMark` の 1 歩 -/

theorem ofL_cons_ne (h : BT) (l : List BT) (hl : l ≠ []) : BT.ofL (h :: l) = .sum h (BT.ofL l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b t => rfl

theorem replMark_D (f p : Nat) (a c cc : BT) :
    replMark (f + 1) (BT.D p a) c cc
      = (if (BT.D p a == c) = true then some cc
         else (replMark f a c cc).map (fun aa => BT.D p aa)) := rfl

theorem replMark_sum2 (f : Nat) (L : List BT) (hL : Atoms L) (h2 : 2 ≤ L.length) (c cc : BT) :
    replMark (f + 1) (BT.ofL L) c cc
      = (match L.getLast? with
         | none => none
         | some last => (replMark f last c cc).map (fun ll => BT.ofL (L.dropLast ++ [ll]))) := by
  cases L with
  | nil =>
    have : (2 : Nat) ≤ 0 := h2
    omega
  | cons x tl =>
    cases tl with
    | nil =>
      have : (2 : Nat) ≤ 1 := h2
      omega
    | cons y rest =>
      have htoL : (BT.sum x (BT.ofL (y :: rest))).toL = x :: y :: rest := toL_ofL _ hL
      show (match ((BT.sum x (BT.ofL (y :: rest))).toL).getLast? with
            | none => none
            | some last => (replMark f last c cc).map
                (fun ll => BT.ofL (((BT.sum x (BT.ofL (y :: rest))).toL).dropLast ++ [ll]))) = _
      rw [htoL]

theorem replMark_last (f : Nat) (L : List BT) (hL : Atoms L) (hne : L ≠ [])
    (p : Nat) (a c cc : BT) :
    replMark (f + 1) (BT.ofL (L ++ [BT.D p a])) c cc
      = (replMark f (BT.D p a) c cc).map (fun ll => BT.ofL (L ++ [ll])) := by
  have hA : Atoms (L ++ [BT.D p a]) := atoms_append L _ hL (atoms_single p a)
  have h2 : 2 ≤ (L ++ [BT.D p a]).length := by
    cases L with
    | nil => exact absurd rfl hne
    | cons h t =>
      have h1 : ([BT.D p a] : List BT).length = 1 := rfl
      show 2 ≤ (h :: (t ++ [BT.D p a])).length
      show 2 ≤ (t ++ [BT.D p a]).length + 1
      rw [List.length_append, h1]
      omega
  rw [replMark_sum2 f (L ++ [BT.D p a]) hA h2 c cc, List.getLast?_concat, List.dropLast_concat]

/-- **差し替えの主張**: 並び `ls` の右端の道の上の `cs` を `ct` に取り替えると `lt` になる。 -/
def SubL (ls lt : List BT) (cs ct : BT) : Prop :=
  ∀ N, BT.size (BT.ofL ls) + 1 ≤ N → replMark N (BT.ofL ls) cs ct = some (BT.ofL lt)

/-- 右端の atom が探しているものそのものだったとき。 -/
theorem subL_hit (pre : List BT) (hpre : Atoms pre) (p : Nat) (a ct : BT) :
    SubL (pre ++ [BT.D p a]) (pre ++ [ct]) (BT.D p a) ct := by
  intro N hN
  cases pre with
  | nil =>
    cases N with
    | zero =>
      have h0 : BT.size (BT.ofL ([] ++ [BT.D p a])) + 1 ≤ 0 := hN
      omega
    | succ M =>
      show replMark (M + 1) (BT.D p a) (BT.D p a) ct = some ct
      rw [replMark_D, if_pos (bt_beq_refl _)]
  | cons h tl =>
    have hne : (h :: tl) ≠ [] := List.cons_ne_nil h tl
    have hsz : BT.size (BT.D p a) + 1 ≤ BT.size (BT.ofL ((h :: tl) ++ [BT.D p a])) :=
      size_ofL_last (h :: tl) (BT.D p a) hne
    have hs2 : 1 ≤ BT.size (BT.D p a) := size_pos _
    cases N with
    | zero => omega
    | succ M =>
      cases M with
      | zero => omega
      | succ M2 =>
        rw [replMark_last (M2 + 1) (h :: tl) hpre hne p a _ _, replMark_D,
          if_pos (bt_beq_refl _)]
        rfl

/-- 右端の atom の下へ潜るとき。 -/
theorem subL_desc (pre : List BT) (hpre : Atoms pre) (p : Nat) (as at_ cs ct : BT)
    (hne : ¬ (BT.D p as = cs))
    (hrec : ∀ N, BT.size as + 1 ≤ N → replMark N as cs ct = some at_) :
    SubL (pre ++ [BT.D p as]) (pre ++ [BT.D p at_]) cs ct := by
  have hbeq : ¬ ((BT.D p as == cs) = true) := by
    rw [bt_beq_false _ _ hne]
    exact Bool.noConfusion
  intro N hN
  cases pre with
  | nil =>
    have hsz : BT.size (BT.ofL ([] ++ [BT.D p as])) = 1 + BT.size as := rfl
    rw [hsz] at hN
    cases N with
    | zero => omega
    | succ M =>
      show replMark (M + 1) (BT.D p as) cs ct = some (BT.D p at_)
      rw [replMark_D, if_neg hbeq, hrec M (by omega)]
      rfl
  | cons h tl =>
    have hpne : (h :: tl) ≠ [] := List.cons_ne_nil h tl
    have hsz : BT.size (BT.D p as) + 1 ≤ BT.size (BT.ofL ((h :: tl) ++ [BT.D p as])) :=
      size_ofL_last (h :: tl) (BT.D p as) hpne
    have hsz2 : BT.size (BT.D p as) = 1 + BT.size as := rfl
    cases N with
    | zero => omega
    | succ M =>
      cases M with
      | zero => omega
      | succ M2 =>
        rw [replMark_last (M2 + 1) (h :: tl) hpre hpne p as _ _, replMark_D, if_neg hbeq,
          hrec M2 (by omega)]
        rfl

theorem subL_nil (T T' cs ct : BT) (hT : BT.ofL T.toL = T) (hT' : BT.ofL T'.toL = T')
    (h : SubL ([] ++ T.toL) ([] ++ T'.toL) cs ct) :
    ∀ N, BT.size T + 1 ≤ N → replMark N T cs ct = some T' := by
  intro N hN
  have h2 := h N (by rw [List.nil_append, hT]; exact hN)
  rw [List.nil_append, List.nil_append, hT, hT'] at h2
  exact h2

/-! ### 8. 差し替えの補題 -/

/-- **印が意味を持つ位置。** 右端の道の上で、寄与が 1 つの `D` になるもの。 -/
def MOK (w : Nat) (x : B) (i : Nat) : Prop :=
  i ∈ lastSpine x ∧ ∃ p a, markIn w x i = some (BT.D p a)

/-- 前順 `i` 番目の節の寄与 (`bMark` の中身)。 -/
def markG (w : Nat) (x : B) (i : Nat) : BT := (markIn w x i).getD .zero

theorem markIn_some_markG (w : Nat) (x : B) (i : Nat)
    (h : ∃ p a, markIn w x i = some (BT.D p a)) : markIn w x i = some (markG w x i) := by
  obtain ⟨p, a, hpa⟩ := h
  have hg : markG w x i = BT.D p a := by
    show (markIn w x i).getD .zero = _
    rw [hpa]
    rfl
  rw [hpa, hg]

theorem atomsL_bFold_snd : ∀ (x : B) (w : Nat) (a : BT), (bFold w x).2 = some a → AtomsL a := by
  intro x
  induction x with
  | nil =>
    intro w a h
    have h' : (none : Option BT) = some a := h
    exact absurd h'.symm (Option.some_ne_none a)
  | nd u r c ihr _ =>
    intro w a h
    by_cases hw : w < u
    · rw [bFold_nd_lt w u r c hw] at h
      have h' : (none : Option BT) = some a := h
      exact absurd h'.symm (Option.some_ne_none a)
    · rw [bFold_nd_ge w u r c hw] at h
      cases hst : (bFold w r).2 with
      | none =>
        rw [hst] at h
        have ha : a = bplus (bFold w r).1 (bK w u r c) := (Option.some.inj h).symm
        rw [ha]
        exact atomsL_bplus _ _ (atomsL_bArg_bFold r w).2 (atomsL_bK w u r c)
      | some a0 =>
        rw [hst] at h
        have ha : a = bplus a0 (bK w u r c) := (Option.some.inj h).symm
        rw [ha]
        exact atomsL_bplus _ _ (ihr w a0 hst) (atomsL_bK w u r c)

theorem dropLastB_nd_ne (v : Nat) (r a : B) (h : a ≠ .nil) :
    dropLastB (.nd v r a) = .nd v r (dropLastB a) := by
  cases a with
  | nil => exact absurd rfl h
  | nd u b c => rfl

/-- **節の寄与そのものの差し替え。** 帰納法の中心。 -/
theorem subst_K_aux (cc : B) (hcc : cc ≠ .nil)
    (ihc : ∀ (v j : Nat), MOK v (dropLastB cc) j → MOK v cc j →
      (∀ pre, Atoms pre → SubL (pre ++ (bArg v (dropLastB cc)).toL) (pre ++ (bArg v cc).toL)
          (markG v (dropLastB cc) j) (markG v cc j))
      ∧ (∀ pre, Atoms pre →
          SubL (pre ++ (bClose v (bFold v (dropLastB cc))).toL)
               (pre ++ (bClose v (bFold v cc)).toL)
            (markG v (dropLastB cc) j) (markG v cc j)))
    (u u' : Nat) (r' : B) (i : Nat)
    (h1 : MOK u (B.nd u' r' (dropLastB cc)) i) (h2 : MOK u (B.nd u' r' cc) i) :
    (∀ pre, Atoms pre → SubL (pre ++ (bK u u' r' (dropLastB cc)).toL)
                  (pre ++ (bK u u' r' cc).toL)
                  (markG u (B.nd u' r' (dropLastB cc)) i) (markG u (B.nd u' r' cc) i))
              ∧ msz (markG u (B.nd u' r' (dropLastB cc)) i)
                  ≤ msz (bK u u' r' (dropLastB cc)) := by
  have hsp2 : i ∈ sizeB r' :: (lastSpine cc).map (fun k => sizeB r' + 1 + k) := by
    have h := h2.1
    rw [lastSpine_nd] at h
    exact h
  rcases List.mem_cons.mp hsp2 with hbase | hdeep
  · -- 位置は節そのもの
    subst hbase
    have hms : markIn u (B.nd u' r' (dropLastB cc)) (sizeB r')
        = some (bK u u' r' (dropLastB cc)) := markIn_node u u' r' (dropLastB cc)
    have hmt : markIn u (B.nd u' r' cc) (sizeB r') = some (bK u u' r' cc) :=
      markIn_node u u' r' cc
    have hcs : markG u (B.nd u' r' (dropLastB cc)) (sizeB r') = bK u u' r' (dropLastB cc) := by
      show (markIn u (B.nd u' r' (dropLastB cc)) (sizeB r')).getD .zero = _
      rw [hms]
      rfl
    have hct : markG u (B.nd u' r' cc) (sizeB r') = bK u u' r' cc := by
      show (markIn u (B.nd u' r' cc) (sizeB r')).getD .zero = _
      rw [hmt]
      rfl
    obtain ⟨p, a, hpa⟩ := h1.2
    rw [hms] at hpa
    have hKs : bK u u' r' (dropLastB cc) = BT.D p a := Option.some.inj hpa
    obtain ⟨q, b, hqb⟩ := h2.2
    rw [hmt] at hqb
    have hKt : bK u u' r' cc = BT.D q b := Option.some.inj hqb
    refine ⟨?_, ?_⟩
    · intro pre hpre
      rw [hcs, hct, hKs, hKt]
      exact subL_hit pre hpre p a (BT.D q b)
    · rw [hcs]
      exact Nat.le_refl _
  · -- 位置は子の中
    obtain ⟨j, hj2, hje⟩ := List.mem_map.mp hdeep
    have hsp1 : i ∈ sizeB r' :: (lastSpine (dropLastB cc)).map (fun k => sizeB r' + 1 + k) := by
      have h := h1.1
      rw [lastSpine_nd] at h
      exact h
    have hj1 : j ∈ lastSpine (dropLastB cc) := by
      rcases List.mem_cons.mp hsp1 with he | hm
      · exfalso
        have : sizeB r' + 1 + j = i := hje
        omega
      · obtain ⟨j', hj', hje'⟩ := List.mem_map.mp hm
        have hb : sizeB r' + 1 + j' = i := hje'
        have hb2 : sizeB r' + 1 + j = i := hje
        rw [show j = j' from by omega]
        exact hj'
    have hje' : sizeB r' + 1 + j = i := hje
    subst hje'
    have hmks : markIn u (B.nd u' r' (dropLastB cc)) (sizeB r' + 1 + j)
        = markIn u' (dropLastB cc) j := markIn_deep u u' r' (dropLastB cc) j
    have hmkt : markIn u (B.nd u' r' cc) (sizeB r' + 1 + j) = markIn u' cc j :=
      markIn_deep u u' r' cc j
    have hcs : markG u (B.nd u' r' (dropLastB cc)) (sizeB r' + 1 + j)
        = markG u' (dropLastB cc) j := by
      show (markIn u (B.nd u' r' (dropLastB cc)) (sizeB r' + 1 + j)).getD .zero = _
      rw [hmks]
      rfl
    have hct : markG u (B.nd u' r' cc) (sizeB r' + 1 + j) = markG u' cc j := by
      show (markIn u (B.nd u' r' cc) (sizeB r' + 1 + j)).getD .zero = _
      rw [hmkt]
      rfl
    have mok1 : MOK u' (dropLastB cc) j := by
      refine ⟨hj1, ?_⟩
      obtain ⟨p, a, hpa⟩ := h1.2
      rw [hmks] at hpa
      exact ⟨p, a, hpa⟩
    have mok2 : MOK u' cc j := by
      refine ⟨hj2, ?_⟩
      obtain ⟨p, a, hpa⟩ := h2.2
      rw [hmkt] at hpa
      exact ⟨p, a, hpa⟩
    have hmark1 : markIn u' (dropLastB cc) j = some (markG u' (dropLastB cc) j) :=
      markIn_some_markG u' (dropLastB cc) j mok1.2
    have hS := msz_markIn (dropLastB cc) u' j (markG u' (dropLastB cc) j) hmark1
    have hdne : dropLastB cc ≠ .nil := by
      intro hc
      rw [hc] at hj1
      have hz : j ∈ ([] : List Nat) := hj1
      cases hz
    have hccn : ¬ ((cc == .nil) = true) := by
      intro hc
      exact absurd (of_decide_eq_true hc) hcc
    have hdn : ¬ ((dropLastB cc == .nil) = true) := by
      intro hc
      exact absurd (of_decide_eq_true hc) hdne
    have hhead : headLvl (dropLastB cc) = headLvl cc := headLvl_dropLast cc hdne
    have hKs : bK u u' r' (dropLastB cc)
        = (if (u' ≤ u || !(r' == .nil) || headLvl cc ≤ u') = true
           then BT.D u' (bArg u' (dropLastB cc))
           else bClose u' (bFold u' (dropLastB cc))) := by
      show (if (dropLastB cc == .nil) = true then (BT.D u' .zero)
            else if (u' ≤ u || !(r' == .nil) || headLvl (dropLastB cc) ≤ u') = true
                 then BT.D u' (bArg u' (dropLastB cc))
                 else bClose u' (bFold u' (dropLastB cc))) = _
      rw [if_neg hdn, hhead]
    have hKt : bK u u' r' cc
        = (if (u' ≤ u || !(r' == .nil) || headLvl cc ≤ u') = true
           then BT.D u' (bArg u' cc)
           else bClose u' (bFold u' cc)) := by
      show (if (cc == .nil) = true then (BT.D u' .zero)
            else if (u' ≤ u || !(r' == .nil) || headLvl cc ≤ u') = true
                 then BT.D u' (bArg u' cc)
                 else bClose u' (bFold u' cc)) = _
      rw [if_neg hccn]
    by_cases htest : (u' ≤ u || !(r' == .nil) || headLvl cc ≤ u') = true
    · rw [if_pos htest] at hKs hKt
      refine ⟨?_, ?_⟩
      · intro pre hpre
        rw [hcs, hct, hKs, hKt]
        refine subL_desc pre hpre u' (bArg u' (dropLastB cc)) (bArg u' cc) _ _ ?_ ?_
        · intro heq
          have he : msz (BT.D u' (bArg u' (dropLastB cc))) = msz (markG u' (dropLastB cc) j) := by
            rw [heq]
          rw [msz_D] at he
          have := hS.1
          omega
        · exact subL_nil _ _ _ _ (nfSum_bArg u' (dropLastB cc)) (nfSum_bArg u' cc)
            ((ihc u' j mok1 mok2).1 [] (by intro z hz; cases hz))
      · rw [hcs, hKs, msz_D]
        have := hS.1
        omega
    · rw [if_neg htest] at hKs hKt
      refine ⟨?_, ?_⟩
      · intro pre hpre
        rw [hcs, hct, hKs, hKt]
        exact (ihc u' j mok1 mok2).2 pre hpre
      · rw [hcs, hKs]
        exact hS.2

/-- 帰納法の 1 段。子の並び `cc` についての主張から、節 `nd u' r' cc` についての主張を作る。 -/
theorem subst_step (cc : B) (hcc : cc ≠ .nil)
    (ihc : ∀ (v j : Nat), MOK v (dropLastB cc) j → MOK v cc j →
      (∀ pre, Atoms pre → SubL (pre ++ (bArg v (dropLastB cc)).toL) (pre ++ (bArg v cc).toL)
          (markG v (dropLastB cc) j) (markG v cc j))
      ∧ (∀ pre, Atoms pre →
          SubL (pre ++ (bClose v (bFold v (dropLastB cc))).toL)
               (pre ++ (bClose v (bFold v cc)).toL)
            (markG v (dropLastB cc) j) (markG v cc j)))
    (u u' : Nat) (r' : B) (i : Nat)
    (h1 : MOK u (dropLastB (B.nd u' r' cc)) i) (h2 : MOK u (B.nd u' r' cc) i) :
    (∀ pre, Atoms pre → SubL (pre ++ (bArg u (dropLastB (B.nd u' r' cc))).toL)
        (pre ++ (bArg u (B.nd u' r' cc)).toL)
        (markG u (dropLastB (B.nd u' r' cc)) i) (markG u (B.nd u' r' cc) i))
    ∧ (∀ pre, Atoms pre →
        SubL (pre ++ (bClose u (bFold u (dropLastB (B.nd u' r' cc)))).toL)
             (pre ++ (bClose u (bFold u (B.nd u' r' cc))).toL)
          (markG u (dropLastB (B.nd u' r' cc)) i) (markG u (B.nd u' r' cc) i)) := by
  rw [dropLastB_nd_ne u' r' cc hcc] at h1 ⊢
  -- 節の寄与についての主張と、印の重みの上界を、位置で場合分けして作る
  have main := subst_K_aux cc hcc ihc u u' r' i h1 h2
  -- ここから、節の主張を `bArg` と `bClose (bFold ...)` に持ち上げる
  have hAr : AtomsL (bArg u r') := (atomsL_bArg_bFold r' u).1
  have hAf : AtomsL (bClose u (bFold u r')) :=
    atomsL_bClose u (bFold u r') (atomsL_bArg_bFold r' u).2
  refine ⟨?_, ?_⟩
  · intro pre hpre
    rw [bArg_nd, bArg_nd,
      toL_bplus (bArg u r') (bK u u' r' (dropLastB cc)) hAr (atomsL_bK u u' r' (dropLastB cc)),
      toL_bplus (bArg u r') (bK u u' r' cc) hAr (atomsL_bK u u' r' cc),
      ← List.append_assoc, ← List.append_assoc]
    exact main.1 (pre ++ (bArg u r').toL) (atoms_append _ _ hpre hAr)
  · intro pre hpre
    by_cases hw : u < u'
    · rw [bClose_bFold_nd_lt u u' r' (dropLastB cc) hw, bClose_bFold_nd_lt u u' r' cc hw,
        toL_bplus _ _ hAf (atomsL_bK u u' r' (dropLastB cc)),
        toL_bplus _ _ hAf (atomsL_bK u u' r' cc),
        ← List.append_assoc, ← List.append_assoc]
      exact main.1 (pre ++ (bClose u (bFold u r')).toL) (atoms_append _ _ hpre hAf)
    · have hA1 : AtomsL ((bFold u r').1) := (atomsL_bArg_bFold r' u).2
      cases hst : (bFold u r').2 with
      | none =>
        rw [bClose_bFold_nd_none u u' r' (dropLastB cc) hw hst,
          bClose_bFold_nd_none u u' r' cc hw hst,
          toL_bplus _ _ hA1 (atomsL_D u _), toL_bplus _ _ hA1 (atomsL_D u _),
          ← List.append_assoc, ← List.append_assoc]
        refine subL_desc (pre ++ (bFold u r').1.toL) (atoms_append _ _ hpre hA1) u
          (bplus (bFold u r').1 (bK u u' r' (dropLastB cc)))
          (bplus (bFold u r').1 (bK u u' r' cc)) _ _ ?_ ?_
        · intro heq
          have he : msz (BT.D u (bplus (bFold u r').1 (bK u u' r' (dropLastB cc))))
              = msz (markG u (B.nd u' r' (dropLastB cc)) i) := by rw [heq]
          rw [msz_D, msz_bplus] at he
          have := main.2
          omega
        · intro N hN
          exact main.1 (bFold u r').1.toL hA1 N hN
      | some a =>
        rw [bClose_bFold_nd_some u u' r' (dropLastB cc) hw a hst,
          bClose_bFold_nd_some u u' r' cc hw a hst,
          toL_bplus _ _ hA1 (atomsL_D u _), toL_bplus _ _ hA1 (atomsL_D u _),
          ← List.append_assoc, ← List.append_assoc]
        refine subL_desc (pre ++ (bFold u r').1.toL) (atoms_append _ _ hpre hA1) u
          (bplus a (bK u u' r' (dropLastB cc))) (bplus a (bK u u' r' cc)) _ _ ?_ ?_
        · intro heq
          have he : msz (BT.D u (bplus a (bK u u' r' (dropLastB cc))))
              = msz (markG u (B.nd u' r' (dropLastB cc)) i) := by rw [heq]
          rw [msz_D, msz_bplus] at he
          have := main.2
          omega
        · intro N hN
          exact main.1 a.toL (atomsL_bFold_snd r' u a hst) N hN

/-- **差し替えの補題、`bArg` と `bClose (bFold ...)` について。** 木の構造帰納法。 -/
theorem subst_PQ : ∀ (y : B) (u i : Nat),
    MOK u (dropLastB y) i → MOK u y i →
    (∀ pre, Atoms pre → SubL (pre ++ (bArg u (dropLastB y)).toL) (pre ++ (bArg u y).toL)
        (markG u (dropLastB y) i) (markG u y i))
    ∧ (∀ pre, Atoms pre →
        SubL (pre ++ (bClose u (bFold u (dropLastB y))).toL)
             (pre ++ (bClose u (bFold u y)).toL)
          (markG u (dropLastB y) i) (markG u y i)) := by
  intro y
  induction y with
  | nil =>
    intro u i _ h2
    have hz : i ∈ ([] : List Nat) := h2.1
    cases hz
  | nd u' r' c _ ihc =>
    intro u i h1 h2
    cases c with
    | nil =>
      exfalso
      have hsp2 : i ∈ sizeB r' :: (lastSpine (.nil : B)).map (fun k => sizeB r' + 1 + k) := by
        have h := h2.1
        rw [lastSpine_nd] at h
        exact h
      have hi : i = sizeB r' := by
        rcases List.mem_cons.mp hsp2 with he | hm
        · exact he
        · have hz : i ∈ ([] : List Nat) := hm
          cases hz
      have h1' : i ∈ lastSpine r' := h1.1
      have := lastSpine_lt r' i h1'
      omega
    | nd u2 r2 c2 =>
      exact subst_step (B.nd u2 r2 c2) (by intro hc; exact B.noConfusion hc) ihc u u' r' i h1 h2

/-- **節の寄与の差し替え**、帰納法の仮定を外した形。 -/
theorem subst_K (cc : B) (hcc : cc ≠ .nil) (u u' : Nat) (r' : B) (i : Nat)
    (h1 : MOK u (B.nd u' r' (dropLastB cc)) i) (h2 : MOK u (B.nd u' r' cc) i) :
    ∀ pre, Atoms pre → SubL (pre ++ (bK u u' r' (dropLastB cc)).toL)
      (pre ++ (bK u u' r' cc).toL)
      (markG u (B.nd u' r' (dropLastB cc)) i) (markG u (B.nd u' r' cc) i) :=
  (subst_K_aux cc hcc (fun v j m1 m2 => subst_PQ cc v j m1 m2) u u' r' i h1 h2).1

/-! ### 9. `markOKB` から `MOK` へ -/

theorem markOKB_ne_leaf (x : B) (i : Nat) (h : markOKB x i = true) : x ≠ .nd 0 .nil .nil := by
  intro hc
  rw [hc] at h
  have hf : markOKB (B.nd 0 .nil .nil) i = false := Bool.and_false _
  rw [hf] at h
  exact Bool.noConfusion h

theorem bMark_eq_markG : ∀ (x : B) (i : Nat), x ≠ .nd 0 .nil .nil → bMark x i = markG 0 x i := by
  intro x i h
  cases x with
  | nil => rfl
  | nd v r c =>
    cases v with
    | zero =>
      cases r with
      | nil =>
        cases c with
        | nil => exact absurd rfl h
        | nd a b cc => rfl
      | nd a b cc => rfl
    | succ k => rfl

theorem markOKB_MOK (x : B) (i : Nat) (h : markOKB x i = true) : MOK 0 x i := by
  have hb := (Bool.and_eq_true _ _).mp h
  refine ⟨of_decide_eq_true hb.1, ?_⟩
  have hm : (match markG 0 x i with | BT.D _ _ => true | _ => false) = true := by
    rw [← bMark_eq_markG x i (markOKB_ne_leaf x i h)]
    exact hb.2
  cases hx : markIn 0 x i with
  | none =>
    exfalso
    have hz : markG 0 x i = BT.zero := by
      show (markIn 0 x i).getD .zero = _
      rw [hx]
      rfl
    rw [hz] at hm
    exact Bool.noConfusion hm
  | some z =>
    have hgz : markG 0 x i = z := by
      show (markIn 0 x i).getD .zero = _
      rw [hx]
      rfl
    rw [hgz] at hm
    cases z with
    | zero => exact absurd hm (by intro hcc; exact Bool.noConfusion hcc)
    | D p a => exact ⟨p, a, by first | exact hx | rfl⟩
    | sum a b => exact absurd hm (by intro hcc; exact Bool.noConfusion hcc)

/-! ### 10. 値の差し替え -/

theorem bK_le (w u : Nat) (r c : B) (h : u ≤ w) : bK w u r c = BT.D u (bArg u c) := by
  show (if (c == .nil) = true then (BT.D u .zero)
        else if (u ≤ w || !(r == .nil) || headLvl c ≤ u) = true then BT.D u (bArg u c)
        else bClose u (bFold u c)) = _
  by_cases hc : (c == (.nil : B)) = true
  · rw [if_pos hc, of_decide_eq_true hc]
    rfl
  · rw [if_neg hc, if_pos (show (u ≤ w || !(r == .nil) || headLvl c ≤ u) = true from by
      rw [decide_eq_true h]
      rfl)]

/-- **§58 の主定理。** 最後の節を足すと、値は「節 `m` の寄与」だけが差し替わる。 -/
theorem subst_bVal (t : B) (m : Nat) (hnf : nfB t = true) (hsz : 1 < sizeB t)
    (hs : markOKB (dropLastB t) m = true) (ht : markOKB t m = true)
    (N : Nat) (hN : BT.size (bVal (dropLastB t)) + 1 ≤ N) :
    replMark N (bVal (dropLastB t)) (bMark (dropLastB t) m) (bMark t m) = some (bVal t) := by
  cases t with
  | nil =>
    exfalso
    have : markOKB (.nil : B) m = false := by
      have hz : (m ∈ lastSpine (.nil : B)) = (m ∈ ([] : List Nat)) := rfl
      show (decide (m ∈ lastSpine (.nil : B)) && _) = false
      rw [show decide (m ∈ lastSpine (.nil : B)) = false from
        decide_eq_false (by intro hcc; cases hcc)]
      rfl
    rw [this] at ht
    exact Bool.noConfusion ht
  | nd v r c =>
    obtain ⟨hv, _, _⟩ := (nfLe_nd_iff 0 v r c).mp hnf
    have hv0 : v = 0 := by omega
    subst hv0
    -- 子は空でない
    have hcne : c ≠ .nil := by
      intro hc
      subst hc
      have hm : m ∈ lastSpine (B.nd 0 r .nil) := (markOKB_MOK _ _ ht).1
      have hm2 : m ∈ lastSpine (dropLastB (B.nd 0 r (.nil : B))) := (markOKB_MOK _ _ hs).1
      rw [lastSpine_nd] at hm
      have hi : m = sizeB r := by
        rcases List.mem_cons.mp hm with he | hz
        · exact he
        · have hzz : m ∈ ([] : List Nat) := hz
          cases hzz
      have h2' : m ∈ lastSpine r := hm2
      have := lastSpine_lt r m h2'
      omega
    have hds : dropLastB (B.nd 0 r c) = B.nd 0 r (dropLastB c) := dropLastB_nd_ne 0 r c hcne
    rw [hds] at hs hN ⊢
    have hsne : (B.nd 0 r (dropLastB c)) ≠ B.nd 0 .nil .nil := markOKB_ne_leaf _ m hs
    -- 値は「前の和 + 節の寄与」
    have hcnil : (c == (.nil : B)) = false := by
      cases hb : (c == (.nil : B)) with
      | true => exact absurd (of_decide_eq_true hb) hcne
      | false => rfl
    have et : bVal (B.nd 0 r c) = bplus (bVal r) (bK 0 0 r c) := by
      show bplus (bVal r) (if (r == .nil && ((0 : Nat) == 0) && (c == .nil)) = true then BT.zero
                           else BT.D 0 (bArg 0 c)) = _
      rw [bK_le 0 0 r c (Nat.le_refl 0),
        if_neg (show ¬ ((r == .nil && ((0 : Nat) == 0) && (c == .nil)) = true) from by
          simp only [hcnil, Bool.and_false]
          exact Bool.noConfusion)]
    have es : bVal (B.nd 0 r (dropLastB c)) = bplus (bVal r) (bK 0 0 r (dropLastB c)) := by
      show bplus (bVal r) (if (r == .nil && ((0 : Nat) == 0) && (dropLastB c == .nil)) = true
                           then BT.zero else BT.D 0 (bArg 0 (dropLastB c))) = _
      rw [bK_le 0 0 r (dropLastB c) (Nat.le_refl 0)]
      by_cases hdn : (dropLastB c == (.nil : B)) = true
      · -- 落とした結果が葉なら、左の兄弟はある
        have hrn : (r == (.nil : B)) = false := by
          cases hb : (r == (.nil : B)) with
          | true =>
            exfalso
            rw [of_decide_eq_true hb, of_decide_eq_true hdn] at hsne
            exact absurd rfl hsne
          | false => rfl
        rw [if_neg (show ¬ ((r == .nil && ((0 : Nat) == 0) && (dropLastB c == .nil)) = true) from by
          simp only [hrn, Bool.false_and]
          exact Bool.noConfusion)]
      · have hdf : (dropLastB c == (.nil : B)) = false := by
          cases hb : (dropLastB c == (.nil : B)) with
          | true => exact absurd hb hdn
          | false => rfl
        rw [if_neg (show ¬ ((r == .nil && ((0 : Nat) == 0) && (dropLastB c == .nil)) = true) from by
          simp only [hdf, Bool.and_false]
          exact Bool.noConfusion)]
    rw [et, es, bMark_eq_markG _ m hsne,
      bMark_eq_markG _ m (markOKB_ne_leaf _ m ht)]
    exact subst_K c hcne 0 0 r m (markOKB_MOK _ _ hs) (markOKB_MOK _ _ ht)
      (bVal r).toL (atomsL_bVal r) N (by
        have hh : BT.size (bplus (bVal r) (bK 0 0 r (dropLastB c))) + 1 ≤ N := by
          rw [← es]
          exact hN
        exact hh)

/-- 燃料を測定の形 (`§57` の `mainDep`) で書いた系。 -/
theorem subst_bVal' (t : B) (m : Nat) (hnf : nfB t = true) (hsz : 1 < sizeB t)
    (hs : markOKB (dropLastB t) m = true) (ht : markOKB t m = true) (N : Nat)
    (hN : BT.size (bVal (dropLastB t)) + BT.size (bMark (dropLastB t) m)
            + BT.size (bMark t m) + 4 ≤ N) :
    replMark N (bVal (dropLastB t)) (bMark (dropLastB t) m) (bMark t m) = some (bVal t) := by
  refine subst_bVal t m hnf hsz hs ht N ?_
  have h1 := size_pos (bMark (dropLastB t) m)
  have h2 := size_pos (bMark t m)
  omega

/-! ### 11. 印の差し替え -/

theorem lastSpine_nd_cases (u' : Nat) (r' cc : B) (i : Nat) (h : i ∈ lastSpine (B.nd u' r' cc)) :
    i = sizeB r' ∨ ∃ j, j ∈ lastSpine cc ∧ i = sizeB r' + 1 + j := by
  rw [lastSpine_nd] at h
  rcases List.mem_cons.mp h with he | hm
  · exact Or.inl he
  · obtain ⟨j, hj, hje⟩ := List.mem_map.mp hm
    exact Or.inr ⟨j, hj, hje.symm⟩

theorem markG_node (w u' : Nat) (r' cc : B) :
    markG w (B.nd u' r' cc) (sizeB r') = bK w u' r' cc := by
  show (markIn w (B.nd u' r' cc) (sizeB r')).getD .zero = _
  rw [markIn_node]
  rfl

theorem markG_deep (w u' : Nat) (r' cc : B) (j : Nat) :
    markG w (B.nd u' r' cc) (sizeB r' + 1 + j) = markG u' cc j := by
  show (markIn w (B.nd u' r' cc) (sizeB r' + 1 + j)).getD .zero = _
  rw [markIn_deep]
  rfl

theorem MOK_deep (w u' : Nat) (r' cc : B) (j : Nat)
    (h : MOK w (B.nd u' r' cc) (sizeB r' + 1 + j)) : MOK u' cc j := by
  refine ⟨?_, ?_⟩
  · rcases lastSpine_nd_cases u' r' cc _ h.1 with he | ⟨j', hj', hje⟩
    · omega
    · rw [show j = j' from by omega]
      exact hj'
  · obtain ⟨p, a, hpa⟩ := h.2
    rw [markIn_deep] at hpa
    exact ⟨p, a, hpa⟩

/-- 印の差し替え、帰納法の 1 段。 -/
theorem subst_mark_step (cc : B) (hcc : cc ≠ .nil)
    (ihc : ∀ (v j0 j : Nat), j0 ≤ j → MOK v (dropLastB cc) j0 → MOK v cc j0 →
      MOK v (dropLastB cc) j → MOK v cc j →
      ∀ N, BT.size (markG v (dropLastB cc) j0) + 1 ≤ N →
        replMark N (markG v (dropLastB cc) j0) (markG v (dropLastB cc) j) (markG v cc j)
          = some (markG v cc j0))
    (w u' : Nat) (r' : B) (i0 i : Nat) (hle : i0 ≤ i)
    (h1 : MOK w (B.nd u' r' (dropLastB cc)) i0) (h2 : MOK w (B.nd u' r' cc) i0)
    (h3 : MOK w (B.nd u' r' (dropLastB cc)) i) (h4 : MOK w (B.nd u' r' cc) i)
    (N : Nat) (hN : BT.size (markG w (B.nd u' r' (dropLastB cc)) i0) + 1 ≤ N) :
    replMark N (markG w (B.nd u' r' (dropLastB cc)) i0)
        (markG w (B.nd u' r' (dropLastB cc)) i) (markG w (B.nd u' r' cc) i)
      = some (markG w (B.nd u' r' cc) i0) := by
  rcases lastSpine_nd_cases u' r' cc i0 h2.1 with hbase | ⟨j0, hj0, hi0⟩
  · -- 印の位置は節そのもの: 節の寄与の差し替え
    subst hbase
    obtain ⟨p, a, hpa⟩ := h1.2
    rw [markIn_node] at hpa
    have hKs : bK w u' r' (dropLastB cc) = BT.D p a := Option.some.inj hpa
    obtain ⟨q, b, hqb⟩ := h2.2
    rw [markIn_node] at hqb
    have hKt : bK w u' r' cc = BT.D q b := Option.some.inj hqb
    rw [markG_node, markG_node]
    refine subL_nil _ _ _ _ (by rw [hKs]; rfl) (by rw [hKt]; rfl)
      (subst_K cc hcc w u' r' i h3 h4 [] (by intro z hz; cases hz)) N ?_
    rw [markG_node] at hN
    exact hN
  · -- 印の位置は子の中: 子で帰納法
    have hi : ∃ j, j ∈ lastSpine cc ∧ i = sizeB r' + 1 + j := by
      rcases lastSpine_nd_cases u' r' cc i h4.1 with he | hj
      · exact absurd he (by omega)
      · exact hj
    obtain ⟨j, hj, hie⟩ := hi
    subst hi0
    subst hie
    rw [markG_deep, markG_deep, markG_deep, markG_deep]
    rw [markG_deep] at hN
    exact ihc u' j0 j (by omega) (MOK_deep w u' r' (dropLastB cc) j0 h1)
      (MOK_deep w u' r' cc j0 h2) (MOK_deep w u' r' (dropLastB cc) j h3)
      (MOK_deep w u' r' cc j h4) N hN

/-- **印の差し替え。** 祖先 `i0` の寄与の中でも、同じ取り替えが起きる。 -/
theorem subst_mark_gen : ∀ (x : B) (w i0 i : Nat), i0 ≤ i →
    MOK w (dropLastB x) i0 → MOK w x i0 → MOK w (dropLastB x) i → MOK w x i →
    ∀ N, BT.size (markG w (dropLastB x) i0) + 1 ≤ N →
      replMark N (markG w (dropLastB x) i0) (markG w (dropLastB x) i) (markG w x i)
        = some (markG w x i0) := by
  intro x
  induction x with
  | nil =>
    intro w i0 i _ _ h2 _ _
    have hz : i0 ∈ ([] : List Nat) := h2.1
    cases hz
  | nd u' r' c _ ihc =>
    intro w i0 i hle h1 h2 h3 h4
    cases c with
    | nil =>
      exfalso
      rcases lastSpine_nd_cases u' r' .nil i0 h2.1 with hbase | ⟨j0, hj0, _⟩
      · have h1' : i0 ∈ lastSpine r' := h1.1
        have := lastSpine_lt r' i0 h1'
        omega
      · have hz : j0 ∈ ([] : List Nat) := hj0
        cases hz
    | nd u2 r2 c2 =>
      have hcc : (B.nd u2 r2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [dropLastB_nd_ne u' r' _ hcc] at h1 h3 ⊢
      exact subst_mark_step (B.nd u2 r2 c2) hcc ihc w u' r' i0 i hle h1 h2 h3 h4

/-- **§58 の主定理の相方。** 印の側でも、同じ差し替えが `Mark` を `Mark` に送る。 -/
theorem subst_bMark (t : B) (m0 m : Nat) (hle : m0 ≤ m)
    (hs0 : markOKB (dropLastB t) m0 = true) (ht0 : markOKB t m0 = true)
    (hs : markOKB (dropLastB t) m = true) (ht : markOKB t m = true)
    (N : Nat) (hN : BT.size (bMark (dropLastB t) m0) + 1 ≤ N) :
    replMark N (bMark (dropLastB t) m0) (bMark (dropLastB t) m) (bMark t m)
      = some (bMark t m0) := by
  rw [bMark_eq_markG _ m0 (markOKB_ne_leaf _ m0 hs0)] at hN
  rw [bMark_eq_markG _ m0 (markOKB_ne_leaf _ m0 hs0),
    bMark_eq_markG _ m0 (markOKB_ne_leaf _ m0 ht0),
    bMark_eq_markG _ m (markOKB_ne_leaf _ m hs),
    bMark_eq_markG _ m (markOKB_ne_leaf _ m ht)]
  exact subst_mark_gen t 0 m0 m hle (markOKB_MOK _ _ hs0) (markOKB_MOK _ _ ht0)
    (markOKB_MOK _ _ hs) (markOKB_MOK _ _ ht) N hN

/-- 燃料を測定の形で書いた系。 -/
theorem subst_bMark' (t : B) (m0 m : Nat) (hle : m0 ≤ m)
    (hs0 : markOKB (dropLastB t) m0 = true) (ht0 : markOKB t m0 = true)
    (hs : markOKB (dropLastB t) m = true) (ht : markOKB t m = true) (N : Nat)
    (hN : BT.size (bMark (dropLastB t) m0) + BT.size (bMark (dropLastB t) m)
            + BT.size (bMark t m) + 4 ≤ N) :
    replMark N (bMark (dropLastB t) m0) (bMark (dropLastB t) m) (bMark t m)
      = some (bMark t m0) := by
  refine subst_bMark t m0 m hle hs0 ht0 hs ht N ?_
  have h1 := size_pos (bMark (dropLastB t) m)
  have h2 := size_pos (bMark t m)
  omega

/-! ### 12. 差し替えが起きるなら、印は右端の道の上にある -/

theorem size_mem_toL : ∀ (T x : BT), x ∈ T.toL → BT.size x ≤ BT.size T
  | .zero, x, h => by
      have hz : x ∈ ([] : List BT) := h
      cases hz
  | .D p a, x, h => by
      have h1 : x ∈ [BT.D p a] := h
      rw [List.mem_singleton.mp h1]
      exact Nat.le_refl _
  | .sum a b, x, h => by
      have h1 : x ∈ a.toL ++ b.toL := h
      show BT.size x ≤ 1 + BT.size a + BT.size b
      rcases List.mem_append.mp h1 with hh | hh
      · have := size_mem_toL a x hh
        omega
      · have := size_mem_toL b x hh
        omega

theorem replMark_sum_eq (f : Nat) (x y c cc : BT) :
    replMark (f + 1) (BT.sum x y) c cc
      = (match ((BT.sum x y).toL).getLast? with
         | none => none
         | some last => (replMark f last c cc).map
             (fun ll => BT.ofL (((BT.sum x y).toL).dropLast ++ [ll]))) := rfl

theorem isMarkedBAux_of_replMark : ∀ (f : Nat) (T c cc T' : BT), replMark f T c cc = some T' →
    ∀ g, BT.size T + 1 ≤ g → isMarkedBAux g (some T) c = true := by
  intro f
  induction f with
  | zero =>
    intro T c cc T' h
    have h' : (none : Option BT) = some T' := h
    exact absurd h'.symm (Option.some_ne_none T')
  | succ e ih =>
    intro T c cc T' h g hg
    have hsz := size_pos T
    cases g with
    | zero => omega
    | succ g' =>
      show (if (T == c) = true then true else isMarkedBAux g' (nextMarkedB T) c) = true
      by_cases hbe : (T == c) = true
      · rw [if_pos hbe]
      · rw [if_neg hbe]
        cases T with
        | zero =>
          have h' : (none : Option BT) = some T' := h
          exact absurd h'.symm (Option.some_ne_none T')
        | D p a =>
          rw [replMark_D, if_neg hbe] at h
          cases hr : replMark e a c cc with
          | none =>
            rw [hr] at h
            have h' : (none : Option BT) = some T' := h
            exact absurd h'.symm (Option.some_ne_none T')
          | some a0 =>
            show isMarkedBAux g' (some a) c = true
            refine ih a c cc a0 hr g' ?_
            have he : BT.size (BT.D p a) = 1 + BT.size a := rfl
            omega
        | sum x y =>
          rw [replMark_sum_eq] at h
          cases hl : ((BT.sum x y).toL).getLast? with
          | none =>
            rw [hl] at h
            have h' : (none : Option BT) = some T' := h
            exact absurd h'.symm (Option.some_ne_none T')
          | some last =>
            rw [hl] at h
            have h2 : (replMark e last c cc).map
                (fun ll => BT.ofL (((BT.sum x y).toL).dropLast ++ [ll])) = some T' := h
            cases hr : replMark e last c cc with
            | none =>
              rw [hr] at h2
              have h' : (none : Option BT) = some T' := h2
              exact absurd h'.symm (Option.some_ne_none T')
            | some ll =>
              have hmem : last ∈ x.toL ++ y.toL := List.mem_of_getLast? hl
              have hlt : BT.size last + 1 ≤ BT.size (BT.sum x y) := by
                show BT.size last + 1 ≤ 1 + BT.size x + BT.size y
                rcases List.mem_append.mp hmem with hh | hh
                · have := size_mem_toL x last hh
                  omega
                · have := size_mem_toL y last hh
                  omega
              show isMarkedBAux g' (nextMarkedB (BT.sum x y)) c = true
              rw [show nextMarkedB (BT.sum x y) = some last from hl]
              exact ih last c cc ll hr g' (by omega)

/-- **差し替えができたなら、印は右端の道の上にある。** `§57` の `markVal` の分岐を潰すのに要る。 -/
theorem isMarkedB_of_replMark (f : Nat) (T c cc T' : BT) (h : replMark f T c cc = some T') :
    isMarkedB T c = true := by
  show isMarkedBAux (Trans.Dict.BT.size T + 2) (some T) c = true
  exact isMarkedBAux_of_replMark f T c cc T' h _ (by omega)

/-- 値の側: 印は `bVal (dropLastB t)` の右端の道の上。 -/
theorem isMarkedB_bVal (t : B) (m : Nat) (hnf : nfB t = true) (hsz : 1 < sizeB t)
    (hs : markOKB (dropLastB t) m = true) (ht : markOKB t m = true) :
    isMarkedB (bVal (dropLastB t)) (bMark (dropLastB t) m) = true :=
  isMarkedB_of_replMark _ _ _ _ _
    (subst_bVal t m hnf hsz hs ht (BT.size (bVal (dropLastB t)) + 1) (Nat.le_refl _))

/-- 印の側: 祖先 `m0` の印の右端の道の上に `m` の印がある。 -/
theorem isMarkedB_bMark (t : B) (m0 m : Nat) (hle : m0 ≤ m)
    (hs0 : markOKB (dropLastB t) m0 = true) (ht0 : markOKB t m0 = true)
    (hs : markOKB (dropLastB t) m = true) (ht : markOKB t m = true) :
    isMarkedB (bMark (dropLastB t) m0) (bMark (dropLastB t) m) = true :=
  isMarkedB_of_replMark _ _ _ _ _
    (subst_bMark t m0 m hle hs0 ht0 hs ht (BT.size (bMark (dropLastB t) m0) + 1) (Nat.le_refl _))

/-! ### 測定 (凍結)

証明した式をそのまま母集団の上で回したもの。6 と 7 だけは**証明していない**。 -/

-- 1. 主定理が意味を持つ位置の数。
#guard ((popNFB 3 6).map fun t =>
    ((List.range (sizeB t)).filter fun m =>
      decide (1 < sizeB t) && markOKB (dropLastB t) m && markOKB t m).length).foldl (· + ·) 0
  == 1086
-- 2. **主定理** (`subst_bVal`)。燃料は `size (bVal s) + 1`。
#guard (popNFB 3 6).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(decide (1 < sizeB t) && markOKB (dropLastB t) m && markOKB t m)
      || (replMark (Trans.Dict.BT.size (bVal (dropLastB t)) + 1) (bVal (dropLastB t))
            (bMark (dropLastB t) m) (bMark t m) == some (bVal t))
#guard (popNFB 4 6).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(decide (1 < sizeB t) && markOKB (dropLastB t) m && markOKB t m)
      || (replMark (Trans.Dict.BT.size (bVal (dropLastB t)) + 1) (bVal (dropLastB t))
            (bMark (dropLastB t) m) (bMark t m) == some (bVal t))
-- 3. 印の側 (祖先 `m0 ≤ m`) の位置の数。
#guard ((popNFB 3 6).map fun t =>
    ((List.range (sizeB t)).flatMap fun m0 =>
      (List.range (sizeB t)).filter fun m =>
        decide (1 < sizeB t) && decide (m0 ≤ m)
          && markOKB (dropLastB t) m && markOKB t m
          && markOKB (dropLastB t) m0 && markOKB t m0).length).foldl (· + ·) 0
  == 1818
-- 4. **印の側の定理** (`subst_bMark`)。
#guard (popNFB 3 6).all fun t =>
  (List.range (sizeB t)).all fun m0 =>
    (List.range (sizeB t)).all fun m =>
      !(decide (m0 ≤ m) && markOKB (dropLastB t) m && markOKB t m
          && markOKB (dropLastB t) m0 && markOKB t m0)
        || (replMark (Trans.Dict.BT.size (bMark (dropLastB t) m0) + 1)
              (bMark (dropLastB t) m0) (bMark (dropLastB t) m) (bMark t m)
              == some (bMark t m0))
#guard (popNFB 4 6).all fun t =>
  (List.range (sizeB t)).all fun m0 =>
    (List.range (sizeB t)).all fun m =>
      !(decide (m0 ≤ m) && markOKB (dropLastB t) m && markOKB t m
          && markOKB (dropLastB t) m0 && markOKB t m0)
        || (replMark (Trans.Dict.BT.size (bMark (dropLastB t) m0) + 1)
              (bMark (dropLastB t) m0) (bMark (dropLastB t) m) (bMark t m)
              == some (bMark t m0))
-- 5. 証明した系 (`isMarkedB_bMark`): 祖先なら `isMarkedB` は真。
#guard (popNFB 3 6).all fun t =>
  (List.range (sizeB t)).all fun m0 =>
    (List.range (sizeB t)).all fun m =>
      !(decide (m0 ≤ m) && markOKB (dropLastB t) m && markOKB t m
          && markOKB (dropLastB t) m0 && markOKB t m0)
        || isMarkedB (bMark (dropLastB t) m0) (bMark (dropLastB t) m)
-- 6. **証明していない**: 仮定を `isMarkedB` にした形。測定では真。
#guard (popNFB 3 6).all fun t =>
  (List.range (sizeB t)).all fun m0 =>
    (List.range (sizeB t)).all fun m =>
      !(markOKB (dropLastB t) m && markOKB t m && markOKB (dropLastB t) m0 && markOKB t m0
          && isMarkedB (bMark (dropLastB t) m0) (bMark (dropLastB t) m))
        || (replMark (Trans.Dict.BT.size (bMark (dropLastB t) m0) + 1)
              (bMark (dropLastB t) m0) (bMark (dropLastB t) m) (bMark t m)
              == some (bMark t m0))
-- 7. なぜ 6 が 4 の系にならないか: `m < m0` なのに `isMarkedB` が真の位置が 26 か所あり、
--    そこでは 2 つの印が同じ項になっている。
#guard ((popNFB 3 6).map fun t =>
    ((List.range (sizeB t)).flatMap fun m0 =>
      (List.range (sizeB t)).filter fun m =>
        decide (m < m0) && markOKB (dropLastB t) m && markOKB t m
          && markOKB (dropLastB t) m0 && markOKB t m0
          && isMarkedB (bMark (dropLastB t) m0) (bMark (dropLastB t) m)).length).foldl (· + ·) 0
  == 26
#guard (popNFB 3 6).all fun t =>
  (List.range (sizeB t)).all fun m0 =>
    (List.range (sizeB t)).all fun m =>
      !(decide (m < m0) && markOKB (dropLastB t) m && markOKB t m
          && markOKB (dropLastB t) m0 && markOKB t m0
          && isMarkedB (bMark (dropLastB t) m0) (bMark (dropLastB t) m))
        || (bMark (dropLastB t) m0 == bMark (dropLastB t) m)

-- 8. §59 での使われ方。穴は `jn1 = admB t (j0B t)`、要求される印は `m + 1 < sizeB t` のもの。
--    `m ≤ jn1` の側では `isMarkedB` が真で、祖先版 (`subst_bMark`) がそのまま効く。
#guard (pop6 3 6).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m && decide (m + 1 < sizeB t) && decide (m ≤ admB t (j0B t)))
      || (markOKB (dropLastB t) m && markOKB (dropLastB t) (admB t (j0B t))
          && markOKB t (admB t (j0B t))
          && isMarkedB (bMark (dropLastB t) m) (bMark (dropLastB t) (admB t (j0B t))))
-- 9. `m ≤ jn1` でない位置 (この母集団で 894 中 6 か所) では `isMarkedB` は偽で、
--    §57 の fallback がそのまま答になる。つまり祖先版で §59 は足りる。
#guard (pop6 3 6).all fun t =>
  let M := psM (matB t 0)
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m && decide (m + 1 < sizeB t) && !(decide (m ≤ admB t (j0B t))))
      || (!(isMarkedB (bMark (dropLastB t) m) (bMark (dropLastB t) (admB t (j0B t))))
          && (BT.D (gp1 M (lenI M - 1)).toNat BT.zero == bMark t m))

/-! ### 公理の確認 -/

end

/-! ## §59 THE GLUE, AND THE TYPES 1-6 BRANCH ASSEMBLED

    markOKB_admB_j0   the side conditions: `markOKB s jn1` and `markOKB t jn1`
    mkC2_glue         the glue: `mkC2 M j0 j1 ty (bMark s jn1) = bMark t jn1`
    runAux_main       the branch, `req = none`:   returns `bVal t`, table stays sound
    runAux_main_mark  the branch, `req = some m`: returns `bMark t m`, table stays sound

§57 named the four inputs of the types 1-6 branch on the index side and §58 proved the
substitution lemma they feed.  What was left is the step from `mkC2` — which is written in terms
of the MATRIX — to the index side, and everything here rests on one identity:

    isAdmB t i  =  "§48 does not collapse the node at i"          (`isAdmB_of_node`)

WHAT CARRIES IT.  `nodeAtB` reads the preorder-`i` node off the index as `(parent level, level,
left siblings, children)`; `markIn` is `bK` of exactly that tuple.  Four `ent` lemmas then say
what the neighbouring columns are:

    children ≠ nil  →  column `i+1` is the FIRST child   (depth `+1`, level `headLvl c`)
    children = nil  →  column `i+1` is not deeper
    left siblings = nil, `i ≥ 1`  →  column `i-1` is the PARENT (depth `-1`, level `w`)
    left siblings ≠ nil, `i ≥ 1`  →  column `i-1` is not shallower

so `bothInc t i` is `c ≠ nil ∧ u < headLvl c` and `bothInc t (i-1)` is `r = nil ∧ w < u`, and
`isAdmB` is the negation of §48's third rule verbatim.  Only `i = 0` needs `nfB`: there `isAdmB`
is true unconditionally, and it is the normal form that forces the leftmost top-level node to
level 0, so it cannot be collapsed either.

NOTE THE DIRECTION.  `markOKB t m = (m on lastSpine) ∧ isAdmB t m` is FALSE — measured at 38
positions of `popNFB 3 6`, the smallest `(0,0)(1,1)(2,2)` at `m = 1`, where the node IS collapsed
and its contribution still comes out a single `psi` because the accumulator is empty.  Only
`markOKB_of_spine_adm` — admitted ⟹ `markOKB` — is used, and that is all §59 needs: `adm` walks
DOWN the chain (`admB_spine`, via `lastSpine_pred`) to an admitted position (`isAdmB_admB`), and
`isAdmB_dropLast` carries the admission to `s = dropLastB t` because the columns of `matB s 0`
are the columns of `matB t 0` minus the last one.

THE GLUE.  `mkC2` has six types, but the index side has three shapes, and which one applies is
decided by the BOTTOM of the collapse chain — `botOf`, the last preorder node's `(parent level p,
level uu, left siblings rL)`.  `botSpine` says `j0` is that node's parent and pins the position
relation `j0 + 1 + sizeB rL = j1`, so `j0 + 1 < j1` is exactly `rL ≠ nil`.  When `j0` is admitted
the chain is empty and the argument simply gains a summand.  When it is not, `tele_chain`
telescopes: every node of `jn1+1 … j0` is a first child with a level strictly above its parent's
and its own first child higher still, so it is an only child (`child_single`) and its `bK` equals
the next one's — down to `bClose p (bFold p (nd uu rL nil))` on the `t` side and
`bClose p (bFold p rL)` (or `psi_p(0)` when `rL = nil`) on the `s` side.  The three shapes:

    ty 1, 3, 5   append      `D v (bplus t2 (D uu 0))`
    ty 6         replace     `D v (D uu 0)`                 — `rL = nil`, so `p < uu`
    ty 2, 4      re-expand   `mkC2`'s `t34` splits the last summand back off

The re-expansion is the only place where `mkC2` inspects `t2`.  It asks whether the last
component of `t2` has head `p`; `lastAtom_aux` — the last component of `bK w u r c` has head at
least `u`, and of `(bFold w x).1` strictly above `w` — is what decides that test in both
directions.  16 of the 440 indices are type 2 or 4, and 12 of those take the "keep" side.

THE TWO BRANCHES.  `runAux_main` is then assembly: `run_main_miss_none` (§57) opens the branch,
the two induction hypotheses give `t1 = bVal s` and `c1 = bMark s jn1`, `mkC2_glue` gives
`c2 = bMark t jn1`, and `subst_bVal'` (§58) closes it.  `runAux_main_mark` splits as §58's guards
8 and 9 said it would: for `m ≤ jn1` every side condition holds and `subst_bMark'` applies; past
`jn1` the requested mark sits ON the collapse chain, so `farMark` computes it — `rL` must be `nil`
there, the `t`-side mark is `psi_uu(0)` and the `s`-side mark is `psi_p(0)` — the `isMarkedB` test
fails and §57's fallback is already the answer.

WHAT IS NOT CLAIMED.  Nothing here runs the outer induction: `runAux_main` and
`runAux_main_mark` take the recursive calls' values as hypotheses, exactly as `runAux_sum` (§55)
and `runAux_type0` (§56) do.  `runAux_main_mark`'s third hypothesis is guarded by `m < j1` — the
`m = j1` branch never recurses, and `Mark j1` is not `Allowed` on `s` at all. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### 1. 前順 `i` 番目の節を読む -/

/-- 前順 `i` 番目の節のデータ `(親の段, 段, 左の兄弟, 子)`。`markIn` と同じ再帰。 -/
def nodeAtB (w : Nat) : B → Nat → Option (Nat × Nat × B × B)
  | .nil, _ => none
  | .nd u r c, i =>
      let lr := sizeB r
      if i < lr then nodeAtB w r i
      else if i == lr then some (w, u, r, c)
      else nodeAtB u c (i - lr - 1)

/-- **`markIn` は節のデータの `bK`。** -/
theorem markIn_nodeAtB : ∀ (x : B) (w i : Nat),
    markIn w x i = (nodeAtB w x i).map (fun q => bK q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  intro x
  induction x with
  | nil => intro w i; rfl
  | nd u r c ihr ihc =>
    intro w i
    show (if i < sizeB r then markIn w r i
          else if (i == sizeB r) = true then some (bK w u r c)
          else markIn u c (i - sizeB r - 1))
      = ((if i < sizeB r then nodeAtB w r i
          else if (i == sizeB r) = true then some ((w, u, r, c) : Nat × Nat × B × B)
          else nodeAtB u c (i - sizeB r - 1)).map (fun q => bK q.1 q.2.1 q.2.2.1 q.2.2.2))
    by_cases h1 : i < sizeB r
    · rw [if_pos h1, if_pos h1]
      exact ihr w i
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : (i == sizeB r) = true
      · rw [if_pos h2, if_pos h2]
        rfl
      · rw [if_neg h2, if_neg h2]
        exact ihc u (i - sizeB r - 1)

theorem nodeAtB_isSome : ∀ (x : B) (w i : Nat), i < sizeB x →
    ∃ q, nodeAtB w x i = some q := by
  intro x
  induction x with
  | nil =>
    intro w i h
    exfalso
    have hz : sizeB (.nil : B) = 0 := rfl
    omega
  | nd u r c ihr ihc =>
    intro w i h
    have h' : i < sizeB r + 1 + sizeB c := h
    show ∃ q, (if i < sizeB r then nodeAtB w r i
               else if (i == sizeB r) = true then some ((w, u, r, c) : Nat × Nat × B × B)
               else nodeAtB u c (i - sizeB r - 1)) = some q
    by_cases h1 : i < sizeB r
    · rw [if_pos h1]; exact ihr w i h1
    · rw [if_neg h1]
      by_cases h2 : (i == sizeB r) = true
      · rw [if_pos h2]; exact ⟨_, rfl⟩
      · rw [if_neg h2]
        have hne : i ≠ sizeB r := by
          intro hc; exact h2 (by rw [hc]; exact beq_self_eq_true _)
        exact ihc u (i - sizeB r - 1) (by omega)

theorem nodeAtB_lt : ∀ (x : B) (w i : Nat) (q : Nat × Nat × B × B),
    nodeAtB w x i = some q → i < sizeB x := by
  intro x
  induction x with
  | nil =>
    intro w i q h
    have h' : (none : Option (Nat × Nat × B × B)) = some q := h
    exact absurd h'.symm (Option.some_ne_none q)
  | nd u r c ihr ihc =>
    intro w i q h
    have h' : (if i < sizeB r then nodeAtB w r i
               else if (i == sizeB r) = true then some ((w, u, r, c) : Nat × Nat × B × B)
               else nodeAtB u c (i - sizeB r - 1)) = some q := h
    show i < sizeB r + 1 + sizeB c
    by_cases h1 : i < sizeB r
    · omega
    · rw [if_neg h1] at h'
      by_cases h2 : (i == sizeB r) = true
      · have := eq_of_beq h2; omega
      · rw [if_neg h2] at h'
        have hne : i ≠ sizeB r := by
          intro hc; exact h2 (by rw [hc]; exact beq_self_eq_true _)
        have := ihc u (i - sizeB r - 1) q h'
        omega

/-! ### 2. 節のデータと、隣り合う 2 列 -/

theorem nodeAtB_none (w i : Nat) (q : Nat × Nat × B × B) :
    nodeAtB w .nil i = some q → False := by
  intro h
  have h' : (none : Option (Nat × Nat × B × B)) = some q := h
  exact absurd h'.symm (Option.some_ne_none q)

/-- 先頭の節は左の兄弟を持たず、親の段は外から渡ってきたもの。 -/
theorem nodeAtB_zero : ∀ (x : B) (w : Nat) (q : Nat × Nat × B × B),
    nodeAtB w x 0 = some q → q.1 = w ∧ q.2.2.1 = .nil := by
  intro x
  induction x with
  | nil => intro w q h; exact absurd h (fun hc => nodeAtB_none w 0 q hc)
  | nd u r c ihr _ =>
    intro w q h
    have h' : (if 0 < sizeB r then nodeAtB w r 0
               else if ((0 : Nat) == sizeB r) = true then some ((w, u, r, c) : Nat × Nat × B × B)
               else nodeAtB u c (0 - sizeB r - 1)) = some q := h
    by_cases h1 : 0 < sizeB r
    · rw [if_pos h1] at h'
      exact ihr w q h'
    · rw [if_neg h1, if_pos (show ((0 : Nat) == sizeB r) = true from by
        rw [show sizeB r = 0 from by omega]; rfl)] at h'
      have hq : q = (w, u, r, c) := (Option.some.inj h').symm
      rw [hq]
      exact ⟨rfl, sizeB_eq_zero r (by omega)⟩

/-- 段は行 1 の成分。 -/
theorem entL_nodeAtB : ∀ (x : B) (w i d : Nat) (q : Nat × Nat × B × B),
    nodeAtB w x i = some q → ent (matB x d) i 1 = q.2.1 := by
  intro x
  induction x with
  | nil => intro w i d q h; exact absurd h (fun hc => nodeAtB_none w i q hc)
  | nd u r c ihr ihc =>
    intro w i d q h
    have h' : (if i < sizeB r then nodeAtB w r i
               else if (i == sizeB r) = true then some ((w, u, r, c) : Nat × Nat × B × B)
               else nodeAtB u c (i - sizeB r - 1)) = some q := h
    by_cases h1 : i < sizeB r
    · rw [if_pos h1] at h'
      rw [ent_nd_left u r c d i 1 h1]
      exact ihr w i d q h'
    · rw [if_neg h1] at h'
      by_cases h2 : (i == sizeB r) = true
      · rw [if_pos h2] at h'
        have hq : q = (w, u, r, c) := (Option.some.inj h').symm
        rw [show i = sizeB r from eq_of_beq h2, ent_nd_node u r c d 1, hq]
        rfl
      · rw [if_neg h2] at h'
        have hne : i ≠ sizeB r := fun hc => h2 (by rw [hc]; exact beq_self_eq_true _)
        obtain ⟨k, hk⟩ : ∃ k, i = sizeB r + 1 + k := ⟨i - sizeB r - 1, by omega⟩
        subst hk
        rw [ent_nd_right u r c d k 1]
        exact ihc u k (d + 1) q (by
          rw [show sizeB r + 1 + k - sizeB r - 1 = k from by omega] at h'
          exact h')

/-- **子があるなら、次の列はその最初の子。** -/
theorem ent_succ_child : ∀ (x : B) (w i d w' u : Nat) (r c : B),
    nodeAtB w x i = some (w', u, r, c) → c ≠ .nil →
    i + 1 < sizeB x ∧ ent (matB x d) (i + 1) 0 = ent (matB x d) i 0 + 1
      ∧ ent (matB x d) (i + 1) 1 = headLvl c := by
  intro x
  induction x with
  | nil => intro w i d w' u r c h _; exact absurd h (fun hc => nodeAtB_none w i _ hc)
  | nd u0 r0 c0 ihr ihc =>
    intro w i d w' u r c h hcn
    have h' : (if i < sizeB r0 then nodeAtB w r0 i
               else if (i == sizeB r0) = true then
                 some ((w, u0, r0, c0) : Nat × Nat × B × B)
               else nodeAtB u0 c0 (i - sizeB r0 - 1)) = some (w', u, r, c) := h
    by_cases h1 : i < sizeB r0
    · rw [if_pos h1] at h'
      obtain ⟨k1, k2, k3⟩ := ihr w i d w' u r c h' hcn
      refine ⟨by show i + 1 < sizeB r0 + 1 + sizeB c0; omega, ?_, ?_⟩
      · rw [ent_nd_left u0 r0 c0 d (i + 1) 0 k1, ent_nd_left u0 r0 c0 d i 0 h1]
        exact k2
      · rw [ent_nd_left u0 r0 c0 d (i + 1) 1 k1]
        exact k3
    · rw [if_neg h1] at h'
      by_cases h2 : (i == sizeB r0) = true
      · rw [if_pos h2] at h'
        have hq := Option.some.inj h'
        have hu : u0 = u := congrArg (fun z => z.2.1) hq
        have hcc : c0 = c := congrArg (fun z => z.2.2.2) hq
        subst hcc
        have hi : i = sizeB r0 := eq_of_beq h2
        subst hi
        have hcpos : 0 < sizeB c0 := sizeB_pos c0 hcn
        refine ⟨by show sizeB r0 + 1 < sizeB r0 + 1 + sizeB c0; omega, ?_, ?_⟩
        · rw [show sizeB r0 + 1 = sizeB r0 + 1 + 0 from by omega,
            ent_nd_right u0 r0 c0 d 0 0, ent_nd_node u0 r0 c0 d 0,
            matB_head0 c0 (d + 1) hcn]
          rfl
        · rw [show sizeB r0 + 1 = sizeB r0 + 1 + 0 from by omega,
            ent_nd_right u0 r0 c0 d 0 1, matB_head1 c0 (d + 1) hcn]
      · rw [if_neg h2] at h'
        have hne : i ≠ sizeB r0 := fun hc => h2 (by rw [hc]; exact beq_self_eq_true _)
        obtain ⟨k, hk⟩ : ∃ k, i = sizeB r0 + 1 + k := ⟨i - sizeB r0 - 1, by omega⟩
        subst hk
        rw [show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega] at h'
        obtain ⟨k1, k2, k3⟩ := ihc u0 k (d + 1) w' u r c h' hcn
        refine ⟨by show sizeB r0 + 1 + k + 1 < sizeB r0 + 1 + sizeB c0; omega, ?_, ?_⟩
        · rw [show sizeB r0 + 1 + k + 1 = sizeB r0 + 1 + (k + 1) from by omega,
            ent_nd_right u0 r0 c0 d (k + 1) 0, ent_nd_right u0 r0 c0 d k 0]
          exact k2
        · rw [show sizeB r0 + 1 + k + 1 = sizeB r0 + 1 + (k + 1) from by omega,
            ent_nd_right u0 r0 c0 d (k + 1) 1]
          exact k3

/-- 子が無いなら、次の列は深くならない。 -/
theorem ent_succ_leaf : ∀ (x : B) (w i d w' u : Nat) (r : B),
    nodeAtB w x i = some (w', u, r, .nil) →
    ent (matB x d) (i + 1) 0 ≤ ent (matB x d) i 0 := by
  intro x
  induction x with
  | nil => intro w i d w' u r h; exact absurd h (fun hc => nodeAtB_none w i _ hc)
  | nd u0 r0 c0 ihr ihc =>
    intro w i d w' u r h
    have h' : (if i < sizeB r0 then nodeAtB w r0 i
               else if (i == sizeB r0) = true then
                 some ((w, u0, r0, c0) : Nat × Nat × B × B)
               else nodeAtB u0 c0 (i - sizeB r0 - 1)) = some (w', u, r, .nil) := h
    by_cases h1 : i < sizeB r0
    · rw [if_pos h1] at h'
      rcases Nat.lt_or_ge (i + 1) (sizeB r0) with hlt | hge
      · rw [ent_nd_left u0 r0 c0 d (i + 1) 0 hlt, ent_nd_left u0 r0 c0 d i 0 h1]
        exact ihr w i d w' u r h'
      · rw [show i + 1 = sizeB r0 from by omega, ent_nd_node u0 r0 c0 d 0,
          ent_nd_left u0 r0 c0 d i 0 h1]
        exact ent_lb r0 d i h1
    · rw [if_neg h1] at h'
      by_cases h2 : (i == sizeB r0) = true
      · rw [if_pos h2] at h'
        have hq := Option.some.inj h'
        have hcc : c0 = .nil := congrArg (fun z => z.2.2.2) hq
        subst hcc
        have hi : i = sizeB r0 := eq_of_beq h2
        subst hi
        rw [ent_zero_of_ge_len (matB (B.nd u0 r0 .nil) d) (sizeB r0 + 1) (by
          rw [sizeB_matB]
          show sizeB r0 + 1 + sizeB (.nil : B) ≤ sizeB r0 + 1
          show sizeB r0 + 1 + 0 ≤ sizeB r0 + 1
          omega)]
        omega
      · rw [if_neg h2] at h'
        have hne : i ≠ sizeB r0 := fun hc => h2 (by rw [hc]; exact beq_self_eq_true _)
        obtain ⟨k, hk⟩ : ∃ k, i = sizeB r0 + 1 + k := ⟨i - sizeB r0 - 1, by omega⟩
        subst hk
        rw [show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega] at h'
        rw [show sizeB r0 + 1 + k + 1 = sizeB r0 + 1 + (k + 1) from by omega,
          ent_nd_right u0 r0 c0 d (k + 1) 0, ent_nd_right u0 r0 c0 d k 0]
        exact ihc u0 k (d + 1) w' u r h'

/-- **左の兄弟が無いなら、前の列は親。** -/
theorem ent_pred_first : ∀ (x : B) (w i d w' u : Nat) (c : B),
    nodeAtB w x i = some (w', u, .nil, c) → 1 ≤ i →
    ent (matB x d) (i - 1) 0 + 1 = ent (matB x d) i 0
      ∧ ent (matB x d) (i - 1) 1 = w' := by
  intro x
  induction x with
  | nil => intro w i d w' u c h _; exact absurd h (fun hc => nodeAtB_none w i _ hc)
  | nd u0 r0 c0 ihr ihc =>
    intro w i d w' u c h hi1
    have h' : (if i < sizeB r0 then nodeAtB w r0 i
               else if (i == sizeB r0) = true then
                 some ((w, u0, r0, c0) : Nat × Nat × B × B)
               else nodeAtB u0 c0 (i - sizeB r0 - 1)) = some (w', u, .nil, c) := h
    by_cases h1 : i < sizeB r0
    · rw [if_pos h1] at h'
      obtain ⟨k1, k2⟩ := ihr w i d w' u c h' hi1
      rw [ent_nd_left u0 r0 c0 d (i - 1) 0 (by omega), ent_nd_left u0 r0 c0 d i 0 h1,
        ent_nd_left u0 r0 c0 d (i - 1) 1 (by omega)]
      exact ⟨k1, k2⟩
    · rw [if_neg h1] at h'
      by_cases h2 : (i == sizeB r0) = true
      · exfalso
        rw [if_pos h2] at h'
        have hq := Option.some.inj h'
        have hr : r0 = .nil := congrArg (fun z => z.2.2.1) hq
        have hi : i = sizeB r0 := eq_of_beq h2
        rw [hr] at hi
        have hz : sizeB (.nil : B) = 0 := rfl
        omega
      · rw [if_neg h2] at h'
        have hne : i ≠ sizeB r0 := fun hc => h2 (by rw [hc]; exact beq_self_eq_true _)
        obtain ⟨k, hk⟩ : ∃ k, i = sizeB r0 + 1 + k := ⟨i - sizeB r0 - 1, by omega⟩
        subst hk
        rw [show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega] at h'
        cases k with
        | zero =>
          have hcz : 0 < sizeB c0 := nodeAtB_lt c0 u0 0 _ h'
          have hcn : c0 ≠ .nil := by
            intro hc
            rw [hc] at hcz
            have hz : sizeB (.nil : B) = 0 := rfl
            omega
          have hw' : w' = u0 := (nodeAtB_zero c0 u0 _ h').1
          rw [show sizeB r0 + 1 + 0 - 1 = sizeB r0 from by omega,
            show sizeB r0 + 1 + 0 = sizeB r0 + 1 + 0 from rfl,
            ent_nd_right u0 r0 c0 d 0 0, ent_nd_node u0 r0 c0 d 0,
            ent_nd_node u0 r0 c0 d 1, matB_head0 c0 (d + 1) hcn, hw']
          exact ⟨rfl, rfl⟩
        | succ k0 =>
          obtain ⟨k1, k2⟩ := ihc u0 (k0 + 1) (d + 1) w' u c h' (by omega)
          rw [show sizeB r0 + 1 + (k0 + 1) - 1 = sizeB r0 + 1 + k0 from by omega,
            ent_nd_right u0 r0 c0 d k0 0, ent_nd_right u0 r0 c0 d (k0 + 1) 0,
            ent_nd_right u0 r0 c0 d k0 1,
            show k0 + 1 - 1 = k0 from by omega] at *
          exact ⟨k1, k2⟩

/-- 左の兄弟があるなら、前の列は浅くない。 -/
theorem ent_pred_sib : ∀ (x : B) (w i d w' u : Nat) (r c : B),
    nodeAtB w x i = some (w', u, r, c) → r ≠ .nil → 1 ≤ i →
    ent (matB x d) i 0 ≤ ent (matB x d) (i - 1) 0 := by
  intro x
  induction x with
  | nil => intro w i d w' u r c h _ _; exact absurd h (fun hc => nodeAtB_none w i _ hc)
  | nd u0 r0 c0 ihr ihc =>
    intro w i d w' u r c h hrn hi1
    have h' : (if i < sizeB r0 then nodeAtB w r0 i
               else if (i == sizeB r0) = true then
                 some ((w, u0, r0, c0) : Nat × Nat × B × B)
               else nodeAtB u0 c0 (i - sizeB r0 - 1)) = some (w', u, r, c) := h
    by_cases h1 : i < sizeB r0
    · rw [if_pos h1] at h'
      rw [ent_nd_left u0 r0 c0 d (i - 1) 0 (by omega), ent_nd_left u0 r0 c0 d i 0 h1]
      exact ihr w i d w' u r c h' hrn hi1
    · rw [if_neg h1] at h'
      by_cases h2 : (i == sizeB r0) = true
      · rw [if_pos h2] at h'
        have hq := Option.some.inj h'
        have hr : r0 = r := congrArg (fun z => z.2.2.1) hq
        have hrp : 0 < sizeB r0 := by
          rw [hr]
          exact sizeB_pos r hrn
        have hi : i = sizeB r0 := eq_of_beq h2
        subst hi
        rw [ent_nd_node u0 r0 c0 d 0, ent_nd_left u0 r0 c0 d (sizeB r0 - 1) 0 (by omega)]
        exact ent_lb r0 d (sizeB r0 - 1) (by omega)
      · rw [if_neg h2] at h'
        have hne : i ≠ sizeB r0 := fun hc => h2 (by rw [hc]; exact beq_self_eq_true _)
        obtain ⟨k, hk⟩ : ∃ k, i = sizeB r0 + 1 + k := ⟨i - sizeB r0 - 1, by omega⟩
        subst hk
        rw [show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega] at h'
        cases k with
        | zero =>
          exfalso
          have := (nodeAtB_zero c0 u0 _ h').2
          exact absurd this hrn
        | succ k0 =>
          rw [show sizeB r0 + 1 + (k0 + 1) - 1 = sizeB r0 + 1 + k0 from by omega,
            ent_nd_right u0 r0 c0 d k0 0, ent_nd_right u0 r0 c0 d (k0 + 1) 0]
          have := ihc u0 (k0 + 1) (d + 1) w' u r c h' hrn (by omega)
          rw [show k0 + 1 - 1 = k0 from by omega] at this
          exact this

/-! ### 3. `isAdm` は「§48 が潰さない」ことに他ならない -/

theorem beqB_false (x y : B) (h : ¬ (x = y)) : (x == y) = false := by
  cases hb : (x == y) with
  | true => exact absurd (of_decide_eq_true hb) h
  | false => rfl

/-- **節が §48 の第 3 分岐 (潰し) に落ちるか。** -/
def collB (w' u : Nat) (r c : B) : Bool :=
  !(c == .nil) && decide (w' < u) && (r == .nil) && decide (u < headLvl c)

theorem bothInc_of_node (t : B) (i w' u : Nat) (r c : B)
    (h : nodeAtB 0 t i = some (w', u, r, c)) :
    bothInc t i = (!(c == .nil) && decide (u < headLvl c)) := by
  have hu : ent (matB t 0) i 1 = u := entL_nodeAtB t 0 i 0 _ h
  by_cases hc : c = .nil
  · subst hc
    have hle := ent_succ_leaf t 0 i 0 w' u r h
    show (decide (ent (matB t 0) i 0 < ent (matB t 0) (i + 1) 0) && _) = _
    rw [show decide (ent (matB t 0) i 0 < ent (matB t 0) (i + 1) 0) = false from
      decide_eq_false (by omega)]
    rfl
  · obtain ⟨_, k2, k3⟩ := ent_succ_child t 0 i 0 w' u r c h hc
    show (decide (ent (matB t 0) i 0 < ent (matB t 0) (i + 1) 0)
      && decide (ent (matB t 0) i 1 < ent (matB t 0) (i + 1) 1)) = _
    rw [k2, k3, hu,
      show decide (ent (matB t 0) i 0 < ent (matB t 0) i 0 + 1) = true from
        decide_eq_true (by omega),
      show (c == (.nil : B)) = false from beqB_false c .nil hc]
    rfl

theorem bothInc_pred_of_node (t : B) (i w' u : Nat) (r c : B)
    (h : nodeAtB 0 t i = some (w', u, r, c)) (hi : 1 ≤ i) :
    bothInc t (i - 1) = ((r == .nil) && decide (w' < u)) := by
  have hu : ent (matB t 0) i 1 = u := entL_nodeAtB t 0 i 0 _ h
  have hsucc : i - 1 + 1 = i := by omega
  by_cases hr : r = .nil
  · subst hr
    obtain ⟨k1, k2⟩ := ent_pred_first t 0 i 0 w' u c h hi
    show (decide (ent (matB t 0) (i - 1) 0 < ent (matB t 0) (i - 1 + 1) 0)
      && decide (ent (matB t 0) (i - 1) 1 < ent (matB t 0) (i - 1 + 1) 1)) = _
    rw [hsucc, k2, hu,
      show decide (ent (matB t 0) (i - 1) 0 < ent (matB t 0) i 0) = true from
        decide_eq_true (by omega),
      show ((.nil : B) == (.nil : B)) = true from rfl]
  · have hge := ent_pred_sib t 0 i 0 w' u r c h hr hi
    show (decide (ent (matB t 0) (i - 1) 0 < ent (matB t 0) (i - 1 + 1) 0) && _) = _
    rw [hsucc,
      show decide (ent (matB t 0) (i - 1) 0 < ent (matB t 0) i 0) = false from
        decide_eq_false (by omega),
      show (r == (.nil : B)) = false from beqB_false r .nil hr]
    rfl

/-- **`isAdm` = 「潰されない」。** `i = 0` を除けば標準形は要らない。 -/
theorem isAdmB_of_node (t : B) (i w' u : Nat) (r c : B)
    (h : nodeAtB 0 t i = some (w', u, r, c)) (hi : 1 ≤ i) :
    isAdmB t i = !(collB w' u r c) := by
  have h1 := bothInc_pred_of_node t i w' u r c h hi
  have h2 := bothInc_of_node t i w' u r c h
  have hd : decide (1 ≤ i) = true := decide_eq_true hi
  by_cases hc : c = .nil
  · subst hc
    have hb2 : bothInc t i = false := by
      rw [h2, show ((.nil : B) == (.nil : B)) = true from rfl]
      rfl
    have hcz : collB w' u r (.nil : B) = false := by
      show ((!((.nil : B) == .nil)) && decide (w' < u) && (r == .nil)
            && decide (u < headLvl (.nil : B))) = false
      rw [show ((.nil : B) == (.nil : B)) = true from rfl]
      rfl
    rw [hcz]
    show (!((decide (1 ≤ i) && bothInc t (i - 1))
      && (decide (i + 1 < sizeB t) && bothInc t i))) = !false
    rw [hb2, Bool.and_false, Bool.and_false]
  · obtain ⟨k1, _, _⟩ := ent_succ_child t 0 i 0 w' u r c h hc
    have hcf : (c == (.nil : B)) = false := beqB_false c .nil hc
    show (!((decide (1 ≤ i) && bothInc t (i - 1))
      && (decide (i + 1 < sizeB t) && bothInc t i)))
      = !((!(c == .nil)) && decide (w' < u) && (r == .nil) && decide (u < headLvl c))
    rw [hd, Bool.true_and, h1, h2, decide_eq_true k1, Bool.true_and, hcf]
    cases (r == (.nil : B)) <;> cases (decide (w' < u)) <;>
      cases (decide (u < headLvl c)) <;> rfl

/-- `i = 0` の節は最左の最上位の節。標準形ならその段は 0 で、潰されない。 -/
theorem collB_zero (t : B) (w' u : Nat) (r c : B) (hnf : nfB t = true) (hne : t ≠ .nil)
    (h : nodeAtB 0 t 0 = some (w', u, r, c)) : collB w' u r c = false := by
  have hw : w' = 0 := (nodeAtB_zero t 0 _ h).1
  have hu : ent (matB t 0) 0 1 = u := entL_nodeAtB t 0 0 0 _ h
  rw [matB_head1 t 0 hne] at hu
  have hle : headLvl t ≤ 0 := headLvl_le t 0 hnf hne
  have hu0 : u = 0 := by omega
  subst hw
  subst hu0
  show ((!(c == .nil)) && decide (0 < 0) && (r == .nil) && decide (0 < headLvl c)) = false
  rw [show decide ((0 : Nat) < 0) = false from decide_eq_false (by omega),
    Bool.and_false, Bool.false_and, Bool.false_and]

theorem isAdmB_zero (t : B) : isAdmB t 0 = true := by
  show (!((decide (1 ≤ 0) && bothInc t (0 - 1))
    && (decide (0 + 1 < sizeB t) && bothInc t 0))) = true
  rw [show decide ((1 : Nat) ≤ 0) = false from decide_eq_false (by omega),
    Bool.false_and, Bool.false_and]
  rfl

/-- 潰されない節では §48 の分岐判定が成り立つ。 -/
theorem bK_test_of_not_coll (w' u : Nat) (r c : B) (h : collB w' u r c = false)
    (hc : ¬ ((c == (.nil : B)) = true)) :
    (u ≤ w' || !(r == .nil) || headLvl c ≤ u) = true := by
    have hcf : (c == (.nil : B)) = false := by
      cases hb : (c == (.nil : B)) with
      | true => exact absurd hb hc
      | false => rfl
    have h0 : ((!(c == .nil)) && decide (w' < u) && (r == .nil)
        && decide (u < headLvl c)) = false := h
    rw [hcf] at h0
    have h'' : (decide (w' < u) && (r == .nil) && decide (u < headLvl c)) = false := h0
    show (decide (u ≤ w') || (!(r == .nil)) || decide (headLvl c ≤ u)) = true
    cases hwu : decide (w' < u) with
    | false =>
      rw [show decide (u ≤ w') = true from decide_eq_true (by
        have := of_decide_eq_false hwu
        omega), Bool.true_or, Bool.true_or]
    | true =>
      rw [hwu, Bool.true_and] at h''
      cases hrn : (r == (.nil : B)) with
      | false =>
        rw [show (!(false : Bool)) = true from rfl, Bool.or_true, Bool.true_or]
      | true =>
        rw [hrn, Bool.true_and] at h''
        rw [show decide (headLvl c ≤ u) = true from decide_eq_true (by
          have := of_decide_eq_false h''
          omega), Bool.or_true]

/-- **潰されない節の寄与は `psi_u(その引数)`。** -/
theorem bK_eq_D_arg (w' u : Nat) (r c : B) (h : collB w' u r c = false) :
    bK w' u r c = BT.D u (bArg u c) := by
  by_cases hc : (c == (.nil : B)) = true
  · rw [of_decide_eq_true hc]
    show (if ((.nil : B) == .nil) = true then (BT.D u .zero)
          else if (u ≤ w' || !(r == .nil) || headLvl (.nil : B) ≤ u) = true
               then BT.D u (bArg u (.nil : B))
          else bClose u (bFold u (.nil : B))) = BT.D u (bArg u (.nil : B))
    rw [if_pos (show ((.nil : B) == (.nil : B)) = true from rfl)]
    rfl
  · show (if (c == .nil) = true then (BT.D u .zero)
          else if (u ≤ w' || !(r == .nil) || headLvl c ≤ u) = true then BT.D u (bArg u c)
          else bClose u (bFold u c)) = _
    rw [if_neg hc, if_pos (bK_test_of_not_coll w' u r c h hc)]

theorem bK_D_of_not_coll (w' u : Nat) (r c : B) (h : collB w' u r c = false) :
    ∃ a, bK w' u r c = BT.D u a := ⟨bArg u c, bK_eq_D_arg w' u r c h⟩

/-- 許された節は潰されない。 -/
theorem notColl_of_adm (x : B) (i w' u : Nat) (r c : B) (hnf : nfB x = true) (hne : x ≠ .nil)
    (hq : nodeAtB 0 x i = some (w', u, r, c)) (hadm : isAdmB x i = true) :
    collB w' u r c = false := by
  cases hm : i with
  | zero =>
    rw [hm] at hq
    exact collB_zero x w' u r c hnf hne hq
  | succ k =>
    rw [hm] at hq hadm
    rw [isAdmB_of_node x (k + 1) w' u r c hq (by omega)] at hadm
    cases hcb : collB w' u r c with
    | true =>
      rw [hcb] at hadm
      exact absurd hadm (by intro hcc; exact Bool.noConfusion hcc)
    | false => rfl

/-- **(N)** 祖先鎖の上の許された節では `Mark` は意味を持つ。 -/
theorem markOKB_of_spine_adm (t : B) (m : Nat) (hnf : nfB t = true)
    (hne : t ≠ .nd 0 .nil .nil) (hsp : m ∈ lastSpine t) (hadm : isAdmB t m = true) :
    markOKB t m = true := by
  have hlt : m < sizeB t := lastSpine_lt t m hsp
  have htne : t ≠ .nil := by
    intro hc
    rw [hc] at hlt
    have hz : sizeB (.nil : B) = 0 := rfl
    omega
  obtain ⟨q, hq⟩ := nodeAtB_isSome t 0 m hlt
  obtain ⟨w', u, r, c⟩ := q
  have hcoll : collB w' u r c = false := notColl_of_adm t m w' u r c hnf htne hq hadm
  obtain ⟨a, hK⟩ := bK_D_of_not_coll w' u r c hcoll
  have hmk : bMark t m = BT.D u a := by
    rw [bMark_eq_markG t m hne]
    show (markIn 0 t m).getD .zero = _
    rw [markIn_nodeAtB t 0 m, hq]
    exact hK
  show (decide (m ∈ lastSpine t) && (match bMark t m with | .D _ _ => true | _ => false)) = true
  rw [decide_eq_true hsp, hmk]
  rfl

/-! ### 4. 祖先鎖を降りる -/

theorem mem_of_mem_dropLast {α : Type _} : ∀ (l : List α) (x : α), x ∈ l.dropLast → x ∈ l
  | [], x, h => by
      have h' : x ∈ ([] : List α) := h
      cases h'
  | [_], x, h => by
      have h' : x ∈ ([] : List α) := h
      cases h'
  | a :: b :: r, x, h => by
      have h' : x ∈ a :: (b :: r).dropLast := h
      rcases List.mem_cons.mp h' with he | hm
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem a (mem_of_mem_dropLast (b :: r) x hm)

theorem mem_dropLast_of_ne_last {α : Type _} : ∀ (l : List α) (x y : α),
    l.getLast? = some y → x ∈ l → ¬ (x = y) → x ∈ l.dropLast := by
  intro l
  induction l with
  | nil =>
    intro x y h _ _
    have h' : (none : Option α) = some y := h
    exact absurd h'.symm (Option.some_ne_none y)
  | cons a tl ih =>
    intro x y h hx hne
    cases tl with
    | nil =>
      exfalso
      have hy : a = y := Option.some.inj h
      have hxa : x = a := List.mem_singleton.mp hx
      exact hne (hxa.trans hy)
    | cons b r =>
      have hgl : (b :: r).getLast? = some y := by
        rw [← getLast?_cons_of_ne_nil a (b :: r) (List.cons_ne_nil b r)]
        exact h
      show x ∈ a :: (b :: r).dropLast
      rcases List.mem_cons.mp hx with he | hm
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem a (ih x y hgl hm hne)

theorem admB_succ (t : B) (k : Nat) :
    admB t (k + 1) = if isAdmB t (k + 1) then k + 1 else admB t k := rfl

/-- **(L)** `adm` は許された位置を返す。 -/
theorem isAdmB_admB (t : B) : ∀ (j : Nat), isAdmB t (admB t j) = true := by
  intro j
  induction j with
  | zero => exact isAdmB_zero t
  | succ k ih =>
    rw [admB_succ]
    by_cases h : isAdmB t (k + 1) = true
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact ih

theorem admB_le (t : B) : ∀ (j : Nat), admB t j ≤ j := by
  intro j
  induction j with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    rw [admB_succ]
    by_cases h : isAdmB t (k + 1) = true
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- **(M')** 最初の子が鎖の上にあるなら、その親も鎖の上。 -/
theorem lastSpine_pred : ∀ (x : B) (w j w' u : Nat) (c : B),
    j ∈ lastSpine x → 1 ≤ j → nodeAtB w x j = some (w', u, .nil, c) →
    j - 1 ∈ lastSpine x := by
  intro x
  induction x with
  | nil =>
    intro w j w' u c hsp _ _
    have h' : j ∈ ([] : List Nat) := hsp
    cases h'
  | nd u0 r0 c0 _ ihc =>
    intro w j w' u c hsp hj1 hnode
    rcases lastSpine_nd_cases u0 r0 c0 j hsp with hbase | ⟨k, hk, hje⟩
    · exfalso
      subst hbase
      have h' : (if sizeB r0 < sizeB r0 then nodeAtB w r0 (sizeB r0)
                 else if ((sizeB r0) == sizeB r0) = true then
                   some ((w, u0, r0, c0) : Nat × Nat × B × B)
                 else nodeAtB u0 c0 (sizeB r0 - sizeB r0 - 1))
          = some (w', u, .nil, c) := hnode
      rw [if_neg (Nat.lt_irrefl _), if_pos (beq_self_eq_true (sizeB r0))] at h'
      have hr : r0 = .nil := congrArg (fun z => z.2.2.1) (Option.some.inj h')
      rw [hr] at hj1
      have hz : sizeB (.nil : B) = 0 := rfl
      omega
    · subst hje
      have h' : (if sizeB r0 + 1 + k < sizeB r0 then nodeAtB w r0 (sizeB r0 + 1 + k)
                 else if ((sizeB r0 + 1 + k) == sizeB r0) = true then
                   some ((w, u0, r0, c0) : Nat × Nat × B × B)
                 else nodeAtB u0 c0 (sizeB r0 + 1 + k - sizeB r0 - 1))
          = some (w', u, .nil, c) := hnode
      rw [if_neg (by omega),
        if_neg (show ¬ (((sizeB r0 + 1 + k) == sizeB r0) = true) from by
          intro hc; exact absurd (eq_of_beq hc) (by omega)),
        show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega] at h'
      rw [lastSpine_nd]
      cases k with
      | zero =>
        exact List.mem_cons.mpr (Or.inl (by omega))
      | succ k0 =>
        refine List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨k0, ?_, by omega⟩))
        have := ihc u0 (k0 + 1) w' u c hk (by omega) h'
        rw [show k0 + 1 - 1 = k0 from by omega] at this
        exact this

/-- **(M)** `adm` は祖先鎖の上を降りる。 -/
theorem admB_spine (t : B) : ∀ (j : Nat), j ∈ lastSpine t → admB t j ∈ lastSpine t := by
  intro j
  induction j with
  | zero => intro h; exact h
  | succ k ih =>
    intro h
    rw [admB_succ]
    by_cases hA : isAdmB t (k + 1) = true
    · rw [if_pos hA]; exact h
    · rw [if_neg hA]
      have hlt : k + 1 < sizeB t := lastSpine_lt t (k + 1) h
      obtain ⟨q, hq⟩ := nodeAtB_isSome t 0 (k + 1) hlt
      obtain ⟨w', u, r, c⟩ := q
      have hE := isAdmB_of_node t (k + 1) w' u r c hq (by omega)
      have hcoll : collB w' u r c = true := by
        cases hcb : collB w' u r c with
        | true => rfl
        | false =>
          exfalso
          rw [hcb] at hE
          exact hA hE
      have hcoll' : ((!(c == .nil)) && decide (w' < u) && (r == .nil)
          && decide (u < headLvl c)) = true := hcoll
      have hr : r = .nil :=
        of_decide_eq_true ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hcoll').1).2
      subst hr
      have hk := lastSpine_pred t 0 (k + 1) w' u c h (by omega) hq
      rw [show k + 1 - 1 = k from by omega] at hk
      exact ih hk

/-- 祖先鎖の最後は最後の節。 -/
theorem lastSpine_getLast : ∀ (x : B), x ≠ .nil →
    (lastSpine x).getLast? = some (sizeB x - 1) := by
  intro x
  induction x with
  | nil => intro h; exact absurd rfl h
  | nd u r c _ ihc =>
    intro _
    cases hc : c with
    | nil =>
      subst hc
      rw [lastSpine_nd]
      show (sizeB r :: (([] : List Nat).map (fun i => sizeB r + 1 + i))).getLast?
        = some (sizeB (B.nd u r .nil) - 1)
      show some (sizeB r) = some (sizeB r + 1 + sizeB (.nil : B) - 1)
      rw [show sizeB (.nil : B) = 0 from rfl,
        show sizeB r + 1 + 0 - 1 = sizeB r from by omega]
    | nd u2 b2 c2 =>
      subst hc
      rw [lastSpine_nd]
      have hne2 : (B.nd u2 b2 c2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
      have hsp : lastSpine (B.nd u2 b2 c2) ≠ [] := lastSpine_ne_nil _ hne2
      have hmapne : ((lastSpine (B.nd u2 b2 c2)).map (fun i => sizeB r + 1 + i)) ≠ [] := by
        intro hcc
        exact hsp (List.map_eq_nil_iff.mp hcc)
      rw [getLast?_cons_of_ne_nil _ _ hmapne, List.getLast?_map, ihc hne2]
      show some (sizeB r + 1 + (sizeB (B.nd u2 b2 c2) - 1))
        = some (sizeB (B.nd u r (B.nd u2 b2 c2)) - 1)
      have hpos : 0 < sizeB (B.nd u2 b2 c2) := sizeB_pos _ hne2
      have : sizeB (B.nd u r (B.nd u2 b2 c2)) = sizeB r + 1 + sizeB (B.nd u2 b2 c2) := rfl
      rw [this, show sizeB r + 1 + (sizeB (B.nd u2 b2 c2) - 1)
        = sizeB r + 1 + sizeB (B.nd u2 b2 c2) - 1 from by omega]

/-- **(Q の道具)** 鎖の最後を落としたものは、最後の節を落とした添字の鎖に入る。 -/
theorem lastSpine_dropLast_sub : ∀ (x : B) (j : Nat),
    j ∈ (lastSpine x).dropLast → j ∈ lastSpine (dropLastB x) := by
  intro x
  induction x with
  | nil =>
    intro j h
    have h' : j ∈ ([] : List Nat) := h
    cases h'
  | nd u r c _ ihc =>
    intro j h
    cases hc : c with
    | nil =>
      exfalso
      rw [hc, lastSpine_nd] at h
      have h' : j ∈ (sizeB r :: (([] : List Nat).map (fun i => sizeB r + 1 + i))).dropLast := h
      have h'' : j ∈ ([] : List Nat) := h'
      cases h''
    | nd u2 b2 c2 =>
      subst hc
      have hne2 : (B.nd u2 b2 c2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
      have hmapne : ((lastSpine (B.nd u2 b2 c2)).map (fun i => sizeB r + 1 + i)) ≠ [] := by
        intro hcc
        exact lastSpine_ne_nil _ hne2 (List.map_eq_nil_iff.mp hcc)
      rw [lastSpine_nd, List.dropLast_cons_of_ne_nil hmapne, ← List.map_dropLast] at h
      rw [dropLastB_nd_ne u r (B.nd u2 b2 c2) hne2, lastSpine_nd]
      rcases List.mem_cons.mp h with he | hm
      · exact List.mem_cons.mpr (Or.inl he)
      · obtain ⟨k, hk, hke⟩ := List.mem_map.mp hm
        exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨k, ihc k hk, hke⟩))

/-! ### 5. 最後の節を落としても、鎖の上の許可は残る -/

theorem ent_dropLast (t : B) (i y : Nat) (h : i + 1 < sizeB t) :
    ent (matB (dropLastB t) 0) i y = ent (matB t 0) i y := by
  have hlen : (matB t 0).length = sizeB t := sizeB_matB t 0
  show (((matB (dropLastB t) 0).getD i []).getD y 0) = (((matB t 0).getD i []).getD y 0)
  rw [matB_dropLast t 0, getD_dropLast (matB t 0) [] i (by omega)]

theorem bothInc_dropLast (t : B) (j : Nat) (h : j + 2 < sizeB t) :
    bothInc (dropLastB t) j = bothInc t j := by
  show (decide (ent (matB (dropLastB t) 0) j 0 < ent (matB (dropLastB t) 0) (j + 1) 0)
      && decide (ent (matB (dropLastB t) 0) j 1 < ent (matB (dropLastB t) 0) (j + 1) 1))
    = (decide (ent (matB t 0) j 0 < ent (matB t 0) (j + 1) 0)
      && decide (ent (matB t 0) j 1 < ent (matB t 0) (j + 1) 1))
  rw [ent_dropLast t j 0 (by omega), ent_dropLast t (j + 1) 0 (by omega),
    ent_dropLast t j 1 (by omega), ent_dropLast t (j + 1) 1 (by omega)]

/-- **許可は最後の節を落としても残る。** -/
theorem isAdmB_dropLast (t : B) (j : Nat) (hne : t ≠ .nil) (h : isAdmB t j = true) :
    isAdmB (dropLastB t) j = true := by
  have hsz : sizeB (dropLastB t) + 1 = sizeB t := sizeB_dropLast t hne
  cases hcond : ((decide (1 ≤ j) && bothInc (dropLastB t) (j - 1))
      && (decide (j + 1 < sizeB (dropLastB t)) && bothInc (dropLastB t) j)) with
  | false =>
    show (!((decide (1 ≤ j) && bothInc (dropLastB t) (j - 1))
      && (decide (j + 1 < sizeB (dropLastB t)) && bothInc (dropLastB t) j))) = true
    rw [hcond]
    rfl
  | true =>
    exfalso
    obtain ⟨hA, hB⟩ := (Bool.and_eq_true _ _).mp hcond
    obtain ⟨hj1, hbp⟩ := (Bool.and_eq_true _ _).mp hA
    obtain ⟨hlt, hbi⟩ := (Bool.and_eq_true _ _).mp hB
    have hj1' : 1 ≤ j := of_decide_eq_true hj1
    have hlt' : j + 1 < sizeB (dropLastB t) := of_decide_eq_true hlt
    have hb1 : bothInc t (j - 1) = true := by
      rw [← bothInc_dropLast t (j - 1) (by omega)]
      exact hbp
    have hb2 : bothInc t j = true := by
      rw [← bothInc_dropLast t j (by omega)]
      exact hbi
    have hbad : isAdmB t j = false := by
      show (!((decide (1 ≤ j) && bothInc t (j - 1))
        && (decide (j + 1 < sizeB t) && bothInc t j))) = false
      rw [hj1, hb1, hb2, decide_eq_true (show j + 1 < sizeB t by omega)]
      rfl
    rw [hbad] at h
    exact Bool.noConfusion h

/-! ### 6. §59 の側条件、まとめて -/

theorem ne_nil_of_size (t : B) (h1 : 1 < sizeB t) : t ≠ .nil := by
  intro hc
  rw [hc] at h1
  have hz : sizeB (.nil : B) = 0 := rfl
  omega

theorem ne_leaf_of_size (t : B) (h1 : 1 < sizeB t) : t ≠ .nd 0 .nil .nil := by
  intro hc
  rw [hc] at h1
  have hz : sizeB (.nd 0 .nil .nil : B) = 1 := rfl
  omega

/-- **(Q)** `j0` は「最後の節を落とした添字」の祖先鎖の上にある。 -/
theorem j0B_mem_dropLast (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) :
    j0B t ∈ (lastSpine t).dropLast :=
  List.mem_of_getLast? (lastSpine_dropLast_ne t h1 hprin)

/-- **(O) 側条件。** `jn1 = adm(j0)` では `Mark` は両側で意味を持つ。 -/
theorem markOKB_admB_j0 (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true)
    (hz : bVal (dropLastB t) ≠ BT.zero) :
    markOKB (dropLastB t) (admB t (j0B t)) = true
      ∧ markOKB t (admB t (j0B t)) = true := by
  have hne : t ≠ .nil := ne_nil_of_size t h1
  have hleaf : t ≠ .nd 0 .nil .nil := ne_leaf_of_size t h1
  have hj0d : j0B t ∈ (lastSpine t).dropLast := j0B_mem_dropLast t h1 hprin
  have hj0 : j0B t ∈ lastSpine t := mem_of_mem_dropLast _ _ hj0d
  have hjn1 : admB t (j0B t) ∈ lastSpine t := admB_spine t (j0B t) hj0
  have hadm : isAdmB t (admB t (j0B t)) = true := isAdmB_admB t (j0B t)
  have hOKt : markOKB t (admB t (j0B t)) = true :=
    markOKB_of_spine_adm t _ hnf hleaf hjn1 hadm
  have hjlt : admB t (j0B t) < sizeB t - 1 := by
    have ha := admB_le t (j0B t)
    have hb := j0B_lt t h1 hprin
    omega
  have hlast : (lastSpine t).getLast? = some (sizeB t - 1) := lastSpine_getLast t hne
  have hjn1d : admB t (j0B t) ∈ (lastSpine t).dropLast :=
    mem_dropLast_of_ne_last _ _ _ hlast hjn1 (by omega)
  have hjn1s : admB t (j0B t) ∈ lastSpine (dropLastB t) := lastSpine_dropLast_sub t _ hjn1d
  have hnfs : nfB (dropLastB t) = true := nfLe_dropLast t 0 hnf
  have hadms : isAdmB (dropLastB t) (admB t (j0B t)) = true := isAdmB_dropLast t _ hne hadm
  have hsleaf : dropLastB t ≠ .nd 0 .nil .nil := by
    intro hc
    exact hz (by rw [hc]; exact bVal_leaf)
  exact ⟨markOKB_of_spine_adm (dropLastB t) _ hnfs hsleaf hjn1s hadms, hOKt⟩

/-! ### 7. 最後の節と、その親 -/

/-- 最後の前順の節の `(親の段, 段, 左の兄弟)`。 -/
def botOf (w : Nat) : B → Nat × Nat × B
  | .nil => (w, 0, .nil)
  | .nd u r c => match c with
                 | .nil => (w, u, r)
                 | _ => botOf u c

/-- 最上位の最後の節の左の兄弟たち。 -/
def lastSibs : B → B
  | .nil => .nil
  | .nd _ r _ => r

theorem lastSpine_eq_nil : ∀ (y : B), lastSpine y = [] ↔ y = .nil := by
  intro y
  cases y with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | nd u r c =>
    exact ⟨fun h => absurd h (lastSpine_ne_nil _ (by intro hc; exact B.noConfusion hc)),
           fun h => absurd h (by intro hc; exact B.noConfusion hc)⟩

/-- 最後の節のデータ。 -/
theorem nodeAtB_last : ∀ (x : B) (w : Nat), x ≠ .nil →
    nodeAtB w x (sizeB x - 1)
      = some ((botOf w x).1, (botOf w x).2.1, (botOf w x).2.2, (.nil : B)) := by
  intro x
  induction x with
  | nil => intro w h; exact absurd rfl h
  | nd u r c _ ihc =>
    intro w _
    cases hc : c with
    | nil =>
      subst hc
      have hsz : sizeB (B.nd u r .nil) - 1 = sizeB r := by
        show sizeB r + 1 + sizeB (.nil : B) - 1 = sizeB r
        show sizeB r + 1 + 0 - 1 = sizeB r
        omega
      rw [hsz]
      show (if sizeB r < sizeB r then nodeAtB w r (sizeB r)
            else if ((sizeB r) == sizeB r) = true then
              some ((w, u, r, (.nil : B)) : Nat × Nat × B × B)
            else nodeAtB u .nil (sizeB r - sizeB r - 1)) = _
      rw [if_neg (Nat.lt_irrefl _), if_pos (beq_self_eq_true (sizeB r))]
      rfl
    | nd u2 b2 c2 =>
      subst hc
      have hne2 : (B.nd u2 b2 c2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
      have hpos : 0 < sizeB (B.nd u2 b2 c2) := sizeB_pos _ hne2
      have hsz : sizeB (B.nd u r (B.nd u2 b2 c2)) - 1
          = sizeB r + 1 + (sizeB (B.nd u2 b2 c2) - 1) := by
        show sizeB r + 1 + sizeB (B.nd u2 b2 c2) - 1 = _
        omega
      rw [hsz]
      show (if sizeB r + 1 + (sizeB (B.nd u2 b2 c2) - 1) < sizeB r then _
            else if ((sizeB r + 1 + (sizeB (B.nd u2 b2 c2) - 1)) == sizeB r) = true then _
            else nodeAtB u (B.nd u2 b2 c2)
              (sizeB r + 1 + (sizeB (B.nd u2 b2 c2) - 1) - sizeB r - 1)) = _
      rw [if_neg (by omega),
        if_neg (show ¬ (((sizeB r + 1 + (sizeB (B.nd u2 b2 c2) - 1)) == sizeB r) = true) from by
          intro hcc; exact absurd (eq_of_beq hcc) (by omega)),
        show sizeB r + 1 + (sizeB (B.nd u2 b2 c2) - 1) - sizeB r - 1
          = sizeB (B.nd u2 b2 c2) - 1 from by omega]
      exact ihc u hne2

/-- **`j0` の節は、最後の節の親。** その子は `nd uu rL nil`、位置の関係も込み。 -/
theorem botSpine : ∀ (x : B) (w j0 : Nat), ((lastSpine x).dropLast).getLast? = some j0 →
    (∃ ww rr, nodeAtB w x j0 = some (ww, (botOf w x).1, rr,
        B.nd (botOf w x).2.1 (botOf w x).2.2 .nil))
      ∧ j0 + 1 + sizeB (botOf w x).2.2 = sizeB x - 1 := by
  intro x
  induction x with
  | nil =>
    intro w j0 h
    have h' : (none : Option Nat) = some j0 := h
    exact absurd h'.symm (Option.some_ne_none j0)
  | nd u r c _ ihc =>
    intro w j0 h
    cases hc : c with
    | nil =>
      exfalso
      rw [hc, lastSpine_nd] at h
      have h' : ((sizeB r :: (([] : List Nat).map (fun i => sizeB r + 1 + i))).dropLast).getLast?
          = some j0 := h
      have h'' : (none : Option Nat) = some j0 := h'
      exact absurd h''.symm (Option.some_ne_none j0)
    | nd u2 b2 c2 =>
      subst hc
      have hne2 : (B.nd u2 b2 c2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
      have hsp2 : lastSpine (B.nd u2 b2 c2) ≠ [] := lastSpine_ne_nil _ hne2
      have hmapne : ((lastSpine (B.nd u2 b2 c2)).map (fun i => sizeB r + 1 + i)) ≠ [] := by
        intro hcc
        exact hsp2 (List.map_eq_nil_iff.mp hcc)
      rw [lastSpine_nd, List.dropLast_cons_of_ne_nil hmapne, ← List.map_dropLast] at h
      have hbot : botOf w (B.nd u r (B.nd u2 b2 c2)) = botOf u (B.nd u2 b2 c2) := rfl
      cases hdl : ((lastSpine (B.nd u2 b2 c2)).dropLast) with
      | nil =>
        rw [hdl] at h
        have hj0 : j0 = sizeB r := by
          have h' : (sizeB r :: (([] : List Nat).map (fun i => sizeB r + 1 + i))).getLast?
              = some j0 := h
          have h'' : some (sizeB r) = some j0 := h'
          exact (Option.some.inj h'').symm
        subst hj0
        -- 鎖の長さ 1: c2 = nil
        have hc2 : c2 = .nil := by
          refine (lastSpine_eq_nil c2).mp ?_
          rw [lastSpine_nd] at hdl
          cases hq : lastSpine c2 with
          | nil => rfl
          | cons z zs =>
            exfalso
            rw [hq] at hdl
            have hd2 : (sizeB b2 :: ((z :: zs).map (fun i => sizeB b2 + 1 + i))).dropLast
                = sizeB b2 :: (((z :: zs).map (fun i => sizeB b2 + 1 + i)).dropLast) := rfl
            rw [hd2] at hdl
            exact absurd hdl (List.cons_ne_nil _ _)
        subst hc2
        have hbot2 : botOf u (B.nd u2 b2 (.nil : B)) = (u, u2, b2) := rfl
        rw [hbot, hbot2]
        refine ⟨⟨w, r, ?_⟩, ?_⟩
        · show (if sizeB r < sizeB r then nodeAtB w r (sizeB r)
                else if ((sizeB r) == sizeB r) = true then
                  some ((w, u, r, B.nd u2 b2 (.nil : B)) : Nat × Nat × B × B)
                else nodeAtB u (B.nd u2 b2 .nil) (sizeB r - sizeB r - 1)) = _
          rw [if_neg (Nat.lt_irrefl _), if_pos (beq_self_eq_true (sizeB r))]
        · show sizeB r + 1 + sizeB b2 = sizeB (B.nd u r (B.nd u2 b2 (.nil : B))) - 1
          show sizeB r + 1 + sizeB b2 = sizeB r + 1 + (sizeB b2 + 1 + sizeB (.nil : B)) - 1
          show sizeB r + 1 + sizeB b2 = sizeB r + 1 + (sizeB b2 + 1 + 0) - 1
          omega
      | cons z zs =>
        have hdlne : ((lastSpine (B.nd u2 b2 c2)).dropLast) ≠ [] := by
          rw [hdl]; exact List.cons_ne_nil _ _
        have hmne : (((lastSpine (B.nd u2 b2 c2)).dropLast).map (fun i => sizeB r + 1 + i)) ≠ [] := by
          intro hcc
          exact hdlne (List.map_eq_nil_iff.mp hcc)
        rw [getLast?_cons_of_ne_nil _ _ hmne, List.getLast?_map] at h
        cases hq : (((lastSpine (B.nd u2 b2 c2)).dropLast).getLast?) with
        | none =>
          exfalso
          rw [hq] at h
          have h' : (none : Option Nat) = some j0 := h
          exact absurd h'.symm (Option.some_ne_none j0)
        | some j0' =>
          rw [hq] at h
          have hj0 : j0 = sizeB r + 1 + j0' := (Option.some.inj h).symm
          subst hj0
          obtain ⟨⟨ww, rr, hnode⟩, hpos⟩ := ihc u j0' hq
          rw [hbot]
          refine ⟨⟨ww, rr, ?_⟩, ?_⟩
          · show (if sizeB r + 1 + j0' < sizeB r then _
                  else if ((sizeB r + 1 + j0') == sizeB r) = true then _
                  else nodeAtB u (B.nd u2 b2 c2) (sizeB r + 1 + j0' - sizeB r - 1)) = _
            rw [if_neg (by omega),
              if_neg (show ¬ (((sizeB r + 1 + j0') == sizeB r) = true) from by
                intro hcc; exact absurd (eq_of_beq hcc) (by omega)),
              show sizeB r + 1 + j0' - sizeB r - 1 = j0' from by omega]
            exact hnode
          · have hpos2 : 0 < sizeB (B.nd u2 b2 c2) := sizeB_pos _ hne2
            show sizeB r + 1 + j0' + 1 + sizeB (botOf u (B.nd u2 b2 c2)).2.2
              = sizeB (B.nd u r (B.nd u2 b2 c2)) - 1
            show sizeB r + 1 + j0' + 1 + sizeB (botOf u (B.nd u2 b2 c2)).2.2
              = sizeB r + 1 + sizeB (B.nd u2 b2 c2) - 1
            omega

/-! ### 8. 鎖の上の節はひとりっ子 -/

theorem lastSpine_ge : ∀ (y : B) (i : Nat), i ∈ lastSpine y → sizeB (lastSibs y) ≤ i := by
  intro y
  cases y with
  | nil =>
    intro i h
    have h' : i ∈ ([] : List Nat) := h
    cases h'
  | nd u r c =>
    intro i h
    rcases lastSpine_nd_cases u r c i h with he | ⟨j, _, hje⟩
    · show sizeB r ≤ i; omega
    · show sizeB r ≤ i; omega

theorem spine_next : ∀ (x : B) (w m w' u : Nat) (r c : B),
    m ∈ lastSpine x → nodeAtB w x m = some (w', u, r, c) → c ≠ .nil →
    ∀ j, j ∈ lastSpine x → m < j → m + 1 + sizeB (lastSibs c) ≤ j := by
  intro x
  induction x with
  | nil =>
    intro w m w' u r c hsp _ _ _ _ _
    have h' : m ∈ ([] : List Nat) := hsp
    cases h'
  | nd u0 r0 c0 _ ihc =>
    intro w m w' u r c hsp hq hcn j hj hmj
    rcases lastSpine_nd_cases u0 r0 c0 m hsp with hbase | ⟨k, hk, hke⟩
    · subst hbase
      have h' : (if sizeB r0 < sizeB r0 then nodeAtB w r0 (sizeB r0)
                 else if ((sizeB r0) == sizeB r0) = true then
                   some ((w, u0, r0, c0) : Nat × Nat × B × B)
                 else nodeAtB u0 c0 (sizeB r0 - sizeB r0 - 1)) = some (w', u, r, c) := hq
      rw [if_neg (Nat.lt_irrefl _), if_pos (beq_self_eq_true (sizeB r0))] at h'
      have hcc : c0 = c := congrArg (fun z => z.2.2.2) (Option.some.inj h')
      subst hcc
      rcases lastSpine_nd_cases u0 r0 c0 j hj with hb2 | ⟨k2, hk2, hke2⟩
      · omega
      · have := lastSpine_ge c0 k2 hk2
        omega
    · subst hke
      have h' : (if sizeB r0 + 1 + k < sizeB r0 then nodeAtB w r0 (sizeB r0 + 1 + k)
                 else if ((sizeB r0 + 1 + k) == sizeB r0) = true then
                   some ((w, u0, r0, c0) : Nat × Nat × B × B)
                 else nodeAtB u0 c0 (sizeB r0 + 1 + k - sizeB r0 - 1)) = some (w', u, r, c) := hq
      rw [if_neg (by omega),
        if_neg (show ¬ (((sizeB r0 + 1 + k) == sizeB r0) = true) from by
          intro hcc2; exact absurd (eq_of_beq hcc2) (by omega)),
        show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega] at h'
      rcases lastSpine_nd_cases u0 r0 c0 j hj with hb2 | ⟨k2, hk2, hke2⟩
      · omega
      · have := ihc u0 k w' u r c hk h' hcn k2 hk2 (by omega)
        omega

/-- 次の節は最初の子。 -/
theorem nodeAtB_succ_child : ∀ (x : B) (w m w' u : Nat) (r c : B),
    nodeAtB w x m = some (w', u, r, c) → c ≠ .nil →
    nodeAtB w x (m + 1) = nodeAtB u c 0 := by
  intro x
  induction x with
  | nil => intro w m w' u r c h _; exact absurd h (fun hcc => nodeAtB_none w m _ hcc)
  | nd u0 r0 c0 ihr ihc =>
    intro w m w' u r c hq hcn
    have h' : (if m < sizeB r0 then nodeAtB w r0 m
               else if (m == sizeB r0) = true then some ((w, u0, r0, c0) : Nat × Nat × B × B)
               else nodeAtB u0 c0 (m - sizeB r0 - 1)) = some (w', u, r, c) := hq
    by_cases h1 : m < sizeB r0
    · rw [if_pos h1] at h'
      have hlt := (ent_succ_child r0 w m 0 w' u r c h' hcn).1
      show (if m + 1 < sizeB r0 then nodeAtB w r0 (m + 1)
            else if ((m + 1) == sizeB r0) = true then
              some ((w, u0, r0, c0) : Nat × Nat × B × B)
            else nodeAtB u0 c0 (m + 1 - sizeB r0 - 1)) = _
      rw [if_pos hlt]
      exact ihr w m w' u r c h' hcn
    · rw [if_neg h1] at h'
      by_cases h2 : (m == sizeB r0) = true
      · rw [if_pos h2] at h'
        have hcc : c0 = c := congrArg (fun z => z.2.2.2) (Option.some.inj h')
        have huu : u0 = u := congrArg (fun z => z.2.1) (Option.some.inj h')
        have hm : m = sizeB r0 := eq_of_beq h2
        rw [← huu, ← hcc, hm]
        show (if sizeB r0 + 1 < sizeB r0 then _
              else if ((sizeB r0 + 1) == sizeB r0) = true then _
              else nodeAtB u0 c0 (sizeB r0 + 1 - sizeB r0 - 1)) = _
        rw [if_neg (by omega),
          if_neg (show ¬ (((sizeB r0 + 1) == sizeB r0) = true) from by
            intro hcc2; exact absurd (eq_of_beq hcc2) (by omega)),
          show sizeB r0 + 1 - sizeB r0 - 1 = 0 from by omega]
      · rw [if_neg h2] at h'
        have hne : m ≠ sizeB r0 := fun hcc => h2 (by rw [hcc]; exact beq_self_eq_true _)
        show (if m + 1 < sizeB r0 then _
              else if ((m + 1) == sizeB r0) = true then _
              else nodeAtB u0 c0 (m + 1 - sizeB r0 - 1)) = _
        rw [if_neg (by omega),
          if_neg (show ¬ (((m + 1) == sizeB r0) = true) from by
            intro hcc2; exact absurd (eq_of_beq hcc2) (by omega)),
          show m + 1 - sizeB r0 - 1 = (m - sizeB r0 - 1) + 1 from by omega]
        exact ihc u0 (m - sizeB r0 - 1) w' u r c h' hcn

theorem nodeAtB_first (w uL : Nat) (cL : B) :
    nodeAtB w (B.nd uL .nil cL) 0 = some (w, uL, (.nil : B), cL) := rfl

/-- **鎖の上の節はひとりっ子。** -/
theorem child_single (x : B) (w m w' u : Nat) (r c : B)
    (hsp : m ∈ lastSpine x) (hq : nodeAtB w x m = some (w', u, r, c)) (hcn : c ≠ .nil)
    (hsp2 : m + 1 ∈ lastSpine x) :
    ∃ uL cL, c = B.nd uL .nil cL ∧ nodeAtB w x (m + 1) = some (u, uL, (.nil : B), cL) := by
  have hz : sizeB (lastSibs c) = 0 := by
    have := spine_next x w m w' u r c hsp hq hcn (m + 1) hsp2 (by omega)
    omega
  cases hcc : c with
  | nil => exact absurd hcc hcn
  | nd uL rL cL =>
    have hrl : rL = .nil := by
      rw [hcc] at hz
      exact sizeB_eq_zero rL hz
    subst hrl
    refine ⟨uL, cL, rfl, ?_⟩
    rw [nodeAtB_succ_child x w m w' u r c hq hcn, hcc, nodeAtB_first]

/-! ### 9. 最後の節を落としたときの節のデータ -/

theorem nodeAtB_dropLast : ∀ (x : B) (w i w' u : Nat) (r c : B),
    i ∈ lastSpine x → i + 1 < sizeB x → nodeAtB w x i = some (w', u, r, c) →
    nodeAtB w (dropLastB x) i = some (w', u, r, dropLastB c) := by
  intro x
  induction x with
  | nil =>
    intro w i w' u r c hsp _ _
    have h' : i ∈ ([] : List Nat) := hsp
    cases h'
  | nd u0 r0 c0 _ ihc =>
    intro w i w' u r c hsp hlt hq
    have hsz : sizeB (B.nd u0 r0 c0) = sizeB r0 + 1 + sizeB c0 := rfl
    rcases lastSpine_nd_cases u0 r0 c0 i hsp with hbase | ⟨k, hk, hke⟩
    · subst hbase
      have h' : (if sizeB r0 < sizeB r0 then nodeAtB w r0 (sizeB r0)
                 else if ((sizeB r0) == sizeB r0) = true then
                   some ((w, u0, r0, c0) : Nat × Nat × B × B)
                 else nodeAtB u0 c0 (sizeB r0 - sizeB r0 - 1)) = some (w', u, r, c) := hq
      rw [if_neg (Nat.lt_irrefl _), if_pos (beq_self_eq_true (sizeB r0))] at h'
      have heq := Option.some.inj h'
      have hw : w = w' := congrArg (fun z => z.1) heq
      have hu : u0 = u := congrArg (fun z => z.2.1) heq
      have hr : r0 = r := congrArg (fun z => z.2.2.1) heq
      have hcc : c0 = c := congrArg (fun z => z.2.2.2) heq
      have hcpos : 0 < sizeB c0 := by omega
      have hcn0 : c0 ≠ .nil := by
        intro hcz
        rw [hcz] at hcpos
        have hz0 : sizeB (.nil : B) = 0 := rfl
        omega
      rw [← hw, ← hu, ← hr, ← hcc, dropLastB_nd_ne u0 r0 c0 hcn0]
      show (if sizeB r0 < sizeB r0 then nodeAtB w r0 (sizeB r0)
            else if ((sizeB r0) == sizeB r0) = true then
              some ((w, u0, r0, dropLastB c0) : Nat × Nat × B × B)
            else nodeAtB u0 (dropLastB c0) (sizeB r0 - sizeB r0 - 1)) = _
      rw [if_neg (Nat.lt_irrefl _), if_pos (beq_self_eq_true (sizeB r0))]
    · subst hke
      have hcn : c0 ≠ .nil := by
        intro hcz
        rw [hcz] at hk
        have h'' : k ∈ ([] : List Nat) := hk
        cases h''
      have h' : (if sizeB r0 + 1 + k < sizeB r0 then nodeAtB w r0 (sizeB r0 + 1 + k)
                 else if ((sizeB r0 + 1 + k) == sizeB r0) = true then
                   some ((w, u0, r0, c0) : Nat × Nat × B × B)
                 else nodeAtB u0 c0 (sizeB r0 + 1 + k - sizeB r0 - 1)) = some (w', u, r, c) := hq
      rw [if_neg (by omega),
        if_neg (show ¬ (((sizeB r0 + 1 + k) == sizeB r0) = true) from by
          intro hcc2; exact absurd (eq_of_beq hcc2) (by omega)),
        show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega] at h'
      rw [dropLastB_nd_ne u0 r0 c0 hcn]
      show (if sizeB r0 + 1 + k < sizeB r0 then _
            else if ((sizeB r0 + 1 + k) == sizeB r0) = true then _
            else nodeAtB u0 (dropLastB c0) (sizeB r0 + 1 + k - sizeB r0 - 1)) = _
      rw [if_neg (by omega),
        if_neg (show ¬ (((sizeB r0 + 1 + k) == sizeB r0) = true) from by
          intro hcc2; exact absurd (eq_of_beq hcc2) (by omega)),
        show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega]
      exact ihc u0 k w' u r c hk (by omega) h'

/-! ### 10. 潰れた鎖を降りる -/

theorem headLvl_nd_nil (u : Nat) (c : B) : headLvl (B.nd u .nil c) = u := rfl

theorem headLvl_nd_ne (v : Nat) (r a : B) (h : r ≠ .nil) : headLvl (B.nd v r a) = headLvl r := by
  cases r with
  | nil => exact absurd rfl h
  | nd v2 r2 a2 => rfl

theorem nfSum_bFold_bClose : ∀ (x : B) (w : Nat),
    NfSum ((bFold w x).1) ∧ NfSum (bClose w (bFold w x)) := by
  intro x
  induction x with
  | nil => intro w; exact ⟨nfSum_zero, nfSum_zero⟩
  | nd u r c ihr _ =>
    intro w
    by_cases hw : w < u
    · have h1 : (bFold w (B.nd u r c)).1
          = bplus (bClose w (bFold w r)) (bK w u r c) := by
        rw [bFold_nd_lt w u r c hw]
      have hn : NfSum (bplus (bClose w (bFold w r)) (bK w u r c)) :=
        nfSum_bplus _ _ (atomsL_bClose w (bFold w r) (atomsL_bArg_bFold r w).2)
          (atomsL_bK w u r c)
      refine ⟨by rw [h1]; exact hn, ?_⟩
      rw [bClose_bFold_nd_lt w u r c hw]
      exact hn
    · cases hst : (bFold w r).2 with
      | none =>
        have h1 : (bFold w (B.nd u r c)).1 = (bFold w r).1 := by
          rw [bFold_nd_ge w u r c hw, hst]
        refine ⟨by rw [h1]; exact (ihr w).1, ?_⟩
        rw [bClose_bFold_nd_none w u r c hw hst]
        exact nfSum_bplus _ _ (atomsL_bArg_bFold r w).2 (atomsL_D _ _)
      | some a =>
        have h1 : (bFold w (B.nd u r c)).1 = (bFold w r).1 := by
          rw [bFold_nd_ge w u r c hw, hst]
        refine ⟨by rw [h1]; exact (ihr w).1, ?_⟩
        rw [bClose_bFold_nd_some w u r c hw a hst]
        exact nfSum_bplus _ _ (atomsL_bArg_bFold r w).2 (atomsL_D _ _)

theorem nfSum_bK (w u : Nat) (r c : B) : NfSum (bK w u r c) := by
  show NfSum (if (c == .nil) = true then (BT.D u .zero)
              else if (u ≤ w || !(r == .nil) || headLvl c ≤ u) = true then BT.D u (bArg u c)
              else bClose u (bFold u c))
  by_cases h1 : (c == (.nil : B)) = true
  · rw [if_pos h1]; exact nfSum_D u .zero
  · rw [if_neg h1]
    by_cases h2 : (u ≤ w || !(r == .nil) || headLvl c ≤ u) = true
    · rw [if_pos h2]; exact nfSum_D u (bArg u c)
    · rw [if_neg h2]; exact (nfSum_bFold_bClose c u).2

theorem bArg_single (w u : Nat) (c : B) : bArg w (B.nd u .nil c) = bK w u .nil c := by
  rw [bArg_nd]
  show bplus BT.zero (bK w u .nil c) = _
  exact bplus_zero_left _ (nfSum_bK w u .nil c)

theorem bClose_bFold_single (w u : Nat) (c : B) (h : w < u) :
    bClose w (bFold w (B.nd u .nil c)) = bK w u .nil c := by
  rw [bClose_bFold_nd_lt w u .nil c h]
  show bplus BT.zero (bK w u .nil c) = _
  exact bplus_zero_left _ (nfSum_bK w u .nil c)

theorem collB_parts (w' u : Nat) (r c : B) (h : collB w' u r c = true) :
    c ≠ .nil ∧ w' < u ∧ r = .nil ∧ u < headLvl c := by
  have h' : ((!(c == .nil)) && decide (w' < u) && (r == .nil)
      && decide (u < headLvl c)) = true := h
  obtain ⟨h1, h4⟩ := (Bool.and_eq_true _ _).mp h'
  obtain ⟨h2, h3⟩ := (Bool.and_eq_true _ _).mp h1
  obtain ⟨hcn, hwu⟩ := (Bool.and_eq_true _ _).mp h2
  refine ⟨?_, of_decide_eq_true hwu, of_decide_eq_true h3, of_decide_eq_true h4⟩
  intro hcz
  rw [hcz, show ((.nil : B) == (.nil : B)) = true from rfl] at hcn
  exact Bool.noConfusion hcn

theorem collB_mk (w' u : Nat) (r c : B) (h1 : c ≠ .nil) (h2 : w' < u) (h3 : r = .nil)
    (h4 : u < headLvl c) : collB w' u r c = true := by
  show ((!(c == .nil)) && decide (w' < u) && (r == .nil) && decide (u < headLvl c)) = true
  rw [beqB_false c .nil h1, show (!(false : Bool)) = true from rfl, decide_eq_true h2,
    h3, show ((.nil : B) == (.nil : B)) = true from rfl, decide_eq_true h4]
  rfl

/-- 潰れた節の寄与は `bClose ∘ bFold`。 -/
theorem bK_coll (w' u : Nat) (r c : B) (h : collB w' u r c = true) :
    bK w' u r c = bClose u (bFold u c) := by
  obtain ⟨h1, h2, h3, h4⟩ := collB_parts w' u r c h
  have htest : (u ≤ w' || !(r == .nil) || headLvl c ≤ u) = false := by
    show (decide (u ≤ w') || (!(r == .nil)) || decide (headLvl c ≤ u)) = false
    rw [decide_eq_false (show ¬(u ≤ w') from by omega), h3,
      show ((.nil : B) == (.nil : B)) = true from rfl,
      show (!(true : Bool)) = false from rfl,
      decide_eq_false (show ¬(headLvl c ≤ u) from by omega)]
    rfl
  show (if (c == .nil) = true then (BT.D u .zero)
        else if (u ≤ w' || !(r == .nil) || headLvl c ≤ u) = true then BT.D u (bArg u c)
        else bClose u (bFold u c)) = _
  rw [if_neg (by rw [beqB_false c .nil h1]; exact Bool.noConfusion),
    if_neg (by rw [htest]; exact Bool.noConfusion)]

theorem coll_of_not_adm' (t : B) (k w' u : Nat) (r c : B) (hk : 1 ≤ k)
    (hq : nodeAtB 0 t k = some (w', u, r, c)) (h : isAdmB t k = false) :
    collB w' u r c = true := by
  rw [isAdmB_of_node t k w' u r c hq hk] at h
  cases hcb : collB w' u r c with
  | true => rfl
  | false => rw [hcb] at h; exact Bool.noConfusion h

theorem pos_of_not_adm (t : B) (k : Nat) (h : isAdmB t k = false) : 1 ≤ k := by
  cases k with
  | zero => rw [isAdmB_zero t] at h; exact Bool.noConfusion h
  | succ _ => omega

/-- 潰れた鎖の上の位置はすべて祖先鎖の上。 -/
theorem chain_spine (t : B) : ∀ (d j0 : Nat), j0 ∈ lastSpine t →
    (∀ k, j0 - d ≤ k → k ≤ j0 → isAdmB t k = false) → (j0 - d) ∈ lastSpine t := by
  intro d
  induction d with
  | zero =>
    intro j0 h _
    rw [show j0 - 0 = j0 from by omega]
    exact h
  | succ e ih =>
    intro j0 hsp hall
    have hprev : (j0 - e) ∈ lastSpine t := ih j0 hsp (fun k h1 h2 => hall k (by omega) h2)
    by_cases hz : j0 - e = 0
    · rw [show j0 - (e + 1) = 0 from by omega, ← hz]
      exact hprev
    · have hlt : (j0 - e) < sizeB t := lastSpine_lt t _ hprev
      have hnad := hall (j0 - e) (by omega) (by omega)
      have hk1 : 1 ≤ j0 - e := pos_of_not_adm t _ hnad
      obtain ⟨q, hq⟩ := nodeAtB_isSome t 0 (j0 - e) hlt
      obtain ⟨w', u, r, c⟩ := q
      have hcoll := coll_of_not_adm' t (j0 - e) w' u r c hk1 hq hnad
      obtain ⟨_, _, hr, _⟩ := collB_parts w' u r c hcoll
      subst hr
      have hp := lastSpine_pred t 0 (j0 - e) w' u c hprev hk1 hq
      rw [show j0 - e - 1 = j0 - (e + 1) from by omega] at hp
      exact hp

theorem chain_spine' (t : B) (j0 m : Nat) (hsp : j0 ∈ lastSpine t)
    (hall : ∀ k, m ≤ k → k ≤ j0 → isAdmB t k = false) :
    ∀ k, m ≤ k → k ≤ j0 → k ∈ lastSpine t := by
  intro k h1 h2
  have hh := chain_spine t (j0 - k) j0 hsp (fun z hz1 hz2 => hall z (by omega) hz2)
  rw [show j0 - (j0 - k) = k from by omega] at hh
  exact hh

/-- **鎖の望遠鏡。** 鎖の上のどの節の寄与も、底の `j0` の寄与に等しい。 -/
theorem tele_chain (t : B) (j0 p uu : Nat) (rL : B)
    (ww rr : Nat × B) (hnode0 : nodeAtB 0 t j0 = some (ww.1, p, rr.2, B.nd uu rL .nil)) :
    ∀ (d m w' u : Nat) (r c : B), m + d = j0 →
    nodeAtB 0 t m = some (w', u, r, c) →
    (∀ k, m ≤ k → k ≤ j0 → isAdmB t k = false) →
    (∀ k, m ≤ k → k ≤ j0 → k ∈ lastSpine t) →
    bK w' u r c = bClose p (bFold p (B.nd uu rL .nil))
      ∧ bK w' u r (dropLastB c)
          = (if rL == .nil then BT.D p BT.zero else bClose p (bFold p rL)) := by
  intro d
  induction d with
  | zero =>
    intro m w' u r c hmd hq hall _
    have hm : m = j0 := by omega
    subst hm
    have heq := Option.some.inj (hnode0.symm.trans hq)
    have hu : p = u := congrArg (fun z => z.2.1) heq
    have hc : B.nd uu rL .nil = c := congrArg (fun z => z.2.2.2) heq
    subst hu
    subst hc
    have hnad := hall m (Nat.le_refl m) (Nat.le_refl m)
    have hk1 : 1 ≤ m := pos_of_not_adm t m hnad
    have hcoll := coll_of_not_adm' t m w' p r _ hk1 hq hnad
    obtain ⟨h1, h2, h3, h4⟩ := collB_parts w' p r _ hcoll
    refine ⟨bK_coll w' p r _ hcoll, ?_⟩
    rw [show dropLastB (B.nd uu rL .nil) = rL from rfl]
    by_cases hrl : rL = .nil
    · subst hrl
      rw [if_pos (show ((.nil : B) == (.nil : B)) = true from rfl)]
      show (if ((.nil : B) == .nil) = true then (BT.D p .zero) else _) = _
      rw [if_pos (show ((.nil : B) == (.nil : B)) = true from rfl)]
    · rw [if_neg (by rw [beqB_false rL .nil hrl]; exact Bool.noConfusion)]
      refine bK_coll w' p r rL (collB_mk w' p r rL hrl h2 h3 ?_)
      rw [headLvl_nd_ne uu rL .nil hrl] at h4
      exact h4
  | succ e ih =>
    intro m w' u r c hmd hq hall hsp
    have hnad := hall m (Nat.le_refl m) (by omega)
    have hk1 : 1 ≤ m := pos_of_not_adm t m hnad
    have hcoll := coll_of_not_adm' t m w' u r c hk1 hq hnad
    obtain ⟨hcn, hwu, hr, hhl⟩ := collB_parts w' u r c hcoll
    have hspm : m ∈ lastSpine t := hsp m (Nat.le_refl m) (by omega)
    have hsp1 : (m + 1) ∈ lastSpine t := hsp (m + 1) (by omega) (by omega)
    obtain ⟨uL, cL, hcc, hnode1⟩ := child_single t 0 m w' u r c hspm hq hcn hsp1
    have huL : u < uL := by
      rw [hcc, headLvl_nd_nil] at hhl
      exact hhl
    have hcoll1 := coll_of_not_adm' t (m + 1) u uL .nil cL (by omega) hnode1
      (hall (m + 1) (by omega) (by omega))
    obtain ⟨hcLn, _, _, _⟩ := collB_parts u uL .nil cL hcoll1
    obtain ⟨ih1, ih2⟩ := ih (m + 1) u uL .nil cL (by omega) hnode1
      (fun k h1 h2 => hall k (by omega) h2) (fun k h1 h2 => hsp k (by omega) h2)
    refine ⟨?_, ?_⟩
    · rw [bK_coll w' u r c hcoll, hcc, bClose_bFold_single u uL cL huL]
      exact ih1
    · rw [hcc, dropLastB_nd_ne uL .nil cL hcLn]
      have hcoll2 : collB w' u r (B.nd uL .nil (dropLastB cL)) = true :=
        collB_mk w' u r _ (by intro hz; exact B.noConfusion hz) hwu hr
          (by rw [headLvl_nd_nil]; exact huL)
      rw [bK_coll w' u r _ hcoll2, bClose_bFold_single u uL (dropLastB cL) huL]
      exact ih2

/-! ### 11. `jn1` の印を、底のデータで書く -/

theorem bMark_bK (x : B) (m w' u : Nat) (r c : B) (hne : x ≠ .nd 0 .nil .nil)
    (hq : nodeAtB 0 x m = some (w', u, r, c)) : bMark x m = bK w' u r c := by
  rw [bMark_eq_markG x m hne]
  show (markIn 0 x m).getD .zero = _
  rw [markIn_nodeAtB x 0 m, hq]
  rfl

/-- 鎖の上の (最後でない) 節は子を持つ。 -/
theorem spine_child_ne : ∀ (x : B) (w m w' u : Nat) (r c : B),
    m ∈ lastSpine x → m + 1 < sizeB x → nodeAtB w x m = some (w', u, r, c) → c ≠ .nil := by
  intro x
  induction x with
  | nil =>
    intro w m w' u r c hsp _ _
    have h' : m ∈ ([] : List Nat) := hsp
    cases h'
  | nd u0 r0 c0 _ ihc =>
    intro w m w' u r c hsp hlt hq
    have hsz : sizeB (B.nd u0 r0 c0) = sizeB r0 + 1 + sizeB c0 := rfl
    rcases lastSpine_nd_cases u0 r0 c0 m hsp with hbase | ⟨k, hk, hke⟩
    · subst hbase
      have h' : (if sizeB r0 < sizeB r0 then nodeAtB w r0 (sizeB r0)
                 else if ((sizeB r0) == sizeB r0) = true then
                   some ((w, u0, r0, c0) : Nat × Nat × B × B)
                 else nodeAtB u0 c0 (sizeB r0 - sizeB r0 - 1)) = some (w', u, r, c) := hq
      rw [if_neg (Nat.lt_irrefl _), if_pos (beq_self_eq_true (sizeB r0))] at h'
      have hcc : c0 = c := congrArg (fun z => z.2.2.2) (Option.some.inj h')
      have hcpos : 0 < sizeB c0 := by omega
      rw [← hcc]
      intro hcz
      rw [hcz] at hcpos
      have hz0 : sizeB (.nil : B) = 0 := rfl
      omega
    · subst hke
      have h' : (if sizeB r0 + 1 + k < sizeB r0 then nodeAtB w r0 (sizeB r0 + 1 + k)
                 else if ((sizeB r0 + 1 + k) == sizeB r0) = true then
                   some ((w, u0, r0, c0) : Nat × Nat × B × B)
                 else nodeAtB u0 c0 (sizeB r0 + 1 + k - sizeB r0 - 1)) = some (w', u, r, c) := hq
      rw [if_neg (by omega),
        if_neg (show ¬ (((sizeB r0 + 1 + k) == sizeB r0) = true) from by
          intro hcc2; exact absurd (eq_of_beq hcc2) (by omega)),
        show sizeB r0 + 1 + k - sizeB r0 - 1 = k from by omega] at h'
      exact ihc u0 k w' u r c hk (by omega) h'

/-- `adm` が飛ばした位置はすべて潰れている。 -/
theorem admB_not_adm (t : B) : ∀ (j k : Nat), admB t j < k → k ≤ j → isAdmB t k = false := by
  intro j
  induction j with
  | zero => intro k h1 h2; exact absurd h1 (by omega)
  | succ e ih =>
    intro k h1 h2
    rw [admB_succ] at h1
    by_cases hA : isAdmB t (e + 1) = true
    · rw [if_pos hA] at h1
      exact absurd h1 (by omega)
    · rw [if_neg hA] at h1
      by_cases hk : k = e + 1
      · rw [hk]
        cases hb : isAdmB t (e + 1) with
        | true => exact absurd hb hA
        | false => rfl
      · exact ih k h1 (by omega)

/-- **`jn1` の印、両側。** -/
theorem markPair (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) (hz : bVal (dropLastB t) ≠ BT.zero) :
    ∃ (w' v : Nat) (r c : B),
      nodeAtB 0 t (admB t (j0B t)) = some (w', v, r, c)
      ∧ bMark t (admB t (j0B t)) = BT.D v (bArg v c)
      ∧ bMark (dropLastB t) (admB t (j0B t)) = BT.D v (bArg v (dropLastB c))
      ∧ (admB t (j0B t) = j0B t →
           c = B.nd (botOf 0 t).2.1 (botOf 0 t).2.2 .nil ∧ v = (botOf 0 t).1)
      ∧ (admB t (j0B t) < j0B t →
           bArg v c = bClose (botOf 0 t).1
               (bFold (botOf 0 t).1 (B.nd (botOf 0 t).2.1 (botOf 0 t).2.2 .nil))
             ∧ bArg v (dropLastB c)
               = (if (botOf 0 t).2.2 == .nil then BT.D (botOf 0 t).1 BT.zero
                  else bClose (botOf 0 t).1 (bFold (botOf 0 t).1 (botOf 0 t).2.2))) := by
  have hne : t ≠ .nil := ne_nil_of_size t h1
  have hleaf : t ≠ .nd 0 .nil .nil := ne_leaf_of_size t h1
  have hsleaf : dropLastB t ≠ .nd 0 .nil .nil := by
    intro hc
    exact hz (by rw [hc]; exact bVal_leaf)
  have hnfs : nfB (dropLastB t) = true := nfLe_dropLast t 0 hnf
  have hsne : dropLastB t ≠ .nil := by
    intro hc
    exact hz (by rw [hc]; rfl)
  have hj0d : j0B t ∈ (lastSpine t).dropLast := j0B_mem_dropLast t h1 hprin
  have hj0 : j0B t ∈ lastSpine t := mem_of_mem_dropLast _ _ hj0d
  have hjn1sp : admB t (j0B t) ∈ lastSpine t := admB_spine t (j0B t) hj0
  have hadm : isAdmB t (admB t (j0B t)) = true := isAdmB_admB t (j0B t)
  have hjle : admB t (j0B t) ≤ j0B t := admB_le t (j0B t)
  have hj0lt : j0B t < sizeB t - 1 := j0B_lt t h1 hprin
  obtain ⟨⟨ww, rr, hnode0⟩, hposrel⟩ := botSpine t 0 (j0B t) (lastSpine_dropLast_ne t h1 hprin)
  obtain ⟨q, hq⟩ := nodeAtB_isSome t 0 (admB t (j0B t)) (by omega)
  obtain ⟨w', v, r, c⟩ := q
  refine ⟨w', v, r, c, hq, ?_, ?_, ?_, ?_⟩
  · rw [bMark_bK t _ w' v r c hleaf hq,
      bK_eq_D_arg w' v r c (notColl_of_adm t _ w' v r c hnf hne hq hadm)]
  · have hqs : nodeAtB 0 (dropLastB t) (admB t (j0B t)) = some (w', v, r, dropLastB c) :=
      nodeAtB_dropLast t 0 _ w' v r c hjn1sp (by omega) hq
    have hadms : isAdmB (dropLastB t) (admB t (j0B t)) = true := isAdmB_dropLast t _ hne hadm
    rw [bMark_bK (dropLastB t) _ w' v r (dropLastB c) hsleaf hqs,
      bK_eq_D_arg w' v r (dropLastB c)
        (notColl_of_adm (dropLastB t) _ w' v r (dropLastB c) hnfs hsne hqs hadms)]
  · intro heq
    rw [heq] at hq
    have hh := Option.some.inj (hnode0.symm.trans hq)
    exact ⟨(congrArg (fun z => z.2.2.2) hh).symm, (congrArg (fun z => z.2.1) hh).symm⟩
  · intro hlt
    have hall : ∀ k, admB t (j0B t) + 1 ≤ k → k ≤ j0B t → isAdmB t k = false :=
      fun k hk1 hk2 => admB_not_adm t (j0B t) k (by omega) hk2
    have hspall : ∀ k, admB t (j0B t) + 1 ≤ k → k ≤ j0B t → k ∈ lastSpine t :=
      chain_spine' t (j0B t) (admB t (j0B t) + 1) hj0 hall
    have hcn : c ≠ .nil := spine_child_ne t 0 _ w' v r c hjn1sp (by omega) hq
    obtain ⟨uL, cL, hcc, hnode1⟩ :=
      child_single t 0 _ w' v r c hjn1sp hq hcn (hspall _ (by omega) (by omega))
    have hcoll1 := coll_of_not_adm' t (admB t (j0B t) + 1) v uL .nil cL (by omega) hnode1
      (hall _ (by omega) (by omega))
    obtain ⟨hcLn, _, _, _⟩ := collB_parts v uL .nil cL hcoll1
    obtain ⟨tt1, tt2⟩ := tele_chain t (j0B t) (botOf 0 t).1 (botOf 0 t).2.1 (botOf 0 t).2.2
      (ww, .nil) (0, rr) hnode0
      (j0B t - (admB t (j0B t) + 1)) (admB t (j0B t) + 1) v uL .nil cL (by omega) hnode1
      (fun k hk1 hk2 => hall k hk1 hk2) (fun k hk1 hk2 => hspall k hk1 hk2)
    refine ⟨?_, ?_⟩
    · rw [hcc, bArg_single v uL cL]
      exact tt1
    · rw [hcc, dropLastB_nd_ne uL .nil cL hcLn, bArg_single v uL (dropLastB cL)]
      exact tt2

/-! ### 12. 底の三つの形 -/

theorem bK_nil (w u : Nat) (r : B) : bK w u r .nil = BT.D u BT.zero := by
  show (if ((.nil : B) == .nil) = true then (BT.D u .zero) else _) = _
  rw [if_pos (show ((.nil : B) == (.nil : B)) = true from rfl)]

/-- 底で `p < uu` のとき: 末尾に足すだけ。 -/
theorem bot_append (p uu : Nat) (rL : B) (h : p < uu) :
    bClose p (bFold p (B.nd uu rL .nil))
      = bplus (bClose p (bFold p rL)) (BT.D uu BT.zero) := by
  rw [bClose_bFold_nd_lt p uu rL .nil h, bK_nil]

/-- 底で `uu ≤ p`、蓄積が空のとき。 -/
theorem bot_none (p uu : Nat) (rL : B) (h : ¬ (p < uu)) (hst : (bFold p rL).2 = none) :
    bClose p (bFold p (B.nd uu rL .nil))
        = bplus (bFold p rL).1 (BT.D p (bplus (bFold p rL).1 (BT.D uu BT.zero)))
      ∧ bClose p (bFold p rL) = (bFold p rL).1 := by
  refine ⟨?_, bClose_none' p (bFold p rL) hst⟩
  rw [bClose_bFold_nd_none p uu rL .nil h hst, bK_nil]

/-- 底で `uu ≤ p`、蓄積があるとき。 -/
theorem bot_some (p uu : Nat) (rL : B) (a : BT) (h : ¬ (p < uu)) (hst : (bFold p rL).2 = some a) :
    bClose p (bFold p (B.nd uu rL .nil))
        = bplus (bFold p rL).1 (BT.D p (bplus a (BT.D uu BT.zero)))
      ∧ bClose p (bFold p rL) = bplus (bFold p rL).1 (BT.D p a) := by
  refine ⟨?_, bClose_some' p (bFold p rL) a hst⟩
  rw [bClose_bFold_nd_some p uu rL .nil h a hst, bK_nil]

/-! ### 13. 和の最後の成分の頭 -/

theorem getLast?_append_right {α : Type _} : ∀ (l1 l2 : List α), l2 ≠ [] →
    (l1 ++ l2).getLast? = l2.getLast? := by
  intro l1
  induction l1 with
  | nil => intro l2 _; rfl
  | cons a rest ih =>
    intro l2 h
    have hne : rest ++ l2 ≠ [] := by
      intro hc
      exact h (List.append_eq_nil_iff.mp hc).2
    show (a :: (rest ++ l2)).getLast? = _
    rw [getLast?_cons_of_ne_nil a (rest ++ l2) hne]
    exact ih l2 h

/-- **和の最後の成分の頭は、その節の段を下回らない。** `mkC2` の `t34` の分岐を潰すのに要る。 -/
theorem lastAtom_aux : ∀ (x : B),
    (∀ (w u : Nat) (r : B), (bK w u r x).toL ≠ []
        ∧ ∀ z, (bK w u r x).toL.getLast? = some z → ∃ s a, z = BT.D s a ∧ u ≤ s)
    ∧ (∀ (w : Nat), (bFold w x).2 = none → x ≠ .nil →
        ((bFold w x).1).toL ≠ []
          ∧ ∀ z, ((bFold w x).1).toL.getLast? = some z → ∃ s a, z = BT.D s a ∧ w < s) := by
  intro x
  induction x with
  | nil =>
    refine ⟨fun w u r => ⟨?_, ?_⟩, fun w _ hne => absurd rfl hne⟩
    · rw [bK_nil]
      show ([BT.D u BT.zero] : List BT) ≠ []
      exact List.cons_ne_nil _ _
    · intro z hz
      rw [bK_nil] at hz
      have hz' : (some (BT.D u BT.zero) : Option BT) = some z := hz
      exact ⟨u, BT.zero, (Option.some.inj hz').symm, Nat.le_refl u⟩
  | nd u1 r1 c1 _ ihc =>
    have h2 : ∀ (w : Nat), (bFold w (B.nd u1 r1 c1)).2 = none → (B.nd u1 r1 c1) ≠ .nil →
        ((bFold w (B.nd u1 r1 c1)).1).toL ≠ []
          ∧ ∀ z, ((bFold w (B.nd u1 r1 c1)).1).toL.getLast? = some z →
              ∃ s a, z = BT.D s a ∧ w < s := by
      intro w hnone _
      by_cases hw : w < u1
      · have h1 : (bFold w (B.nd u1 r1 c1)).1
            = bplus (bClose w (bFold w r1)) (bK w u1 r1 c1) := by
          rw [bFold_nd_lt w u1 r1 c1 hw]
        have hA : AtomsL (bClose w (bFold w r1)) :=
          atomsL_bClose w (bFold w r1) (atomsL_bArg_bFold r1 w).2
        have hB : AtomsL (bK w u1 r1 c1) := atomsL_bK w u1 r1 c1
        have htoL : ((bFold w (B.nd u1 r1 c1)).1).toL
            = (bClose w (bFold w r1)).toL ++ (bK w u1 r1 c1).toL := by
          rw [h1, toL_bplus _ _ hA hB]
        have hKne := (ihc.1 w u1 r1).1
        refine ⟨?_, ?_⟩
        · rw [htoL]
          intro hc
          exact hKne (List.append_eq_nil_iff.mp hc).2
        · intro z hz
          rw [htoL, getLast?_append_right _ _ hKne] at hz
          obtain ⟨s, a, hza, hus⟩ := (ihc.1 w u1 r1).2 z hz
          exact ⟨s, a, hza, by omega⟩
      · exfalso
        cases hst : (bFold w r1).2 with
        | none =>
          have hs2 : (bFold w (B.nd u1 r1 c1)).2
              = some (bplus (bFold w r1).1 (bK w u1 r1 c1)) := by
            rw [bFold_nd_ge w u1 r1 c1 hw, hst]
          rw [hs2] at hnone
          exact absurd hnone (Option.some_ne_none _)
        | some a =>
          have hs2 : (bFold w (B.nd u1 r1 c1)).2 = some (bplus a (bK w u1 r1 c1)) := by
            rw [bFold_nd_ge w u1 r1 c1 hw, hst]
          rw [hs2] at hnone
          exact absurd hnone (Option.some_ne_none _)
    refine ⟨fun w u r => ?_, h2⟩
    by_cases htest : (u ≤ w || !(r == .nil) || headLvl (B.nd u1 r1 c1) ≤ u) = true
    · have hK : bK w u r (B.nd u1 r1 c1) = BT.D u (bArg u (B.nd u1 r1 c1)) := by
        show (if ((B.nd u1 r1 c1) == .nil) = true then (BT.D u .zero)
              else if (u ≤ w || !(r == .nil) || headLvl (B.nd u1 r1 c1) ≤ u) = true
                   then BT.D u (bArg u (B.nd u1 r1 c1))
              else bClose u (bFold u (B.nd u1 r1 c1))) = _
        rw [if_neg (show ¬ (((B.nd u1 r1 c1) == (.nil : B)) = true) from by
          intro hc; exact B.noConfusion (of_decide_eq_true hc)), if_pos htest]
      rw [hK]
      refine ⟨List.cons_ne_nil _ _, ?_⟩
      intro z hz
      have hz' : (some (BT.D u (bArg u (B.nd u1 r1 c1))) : Option BT) = some z := hz
      exact ⟨u, bArg u (B.nd u1 r1 c1), (Option.some.inj hz').symm, Nat.le_refl u⟩
    · have hK : bK w u r (B.nd u1 r1 c1) = bClose u (bFold u (B.nd u1 r1 c1)) := by
        show (if ((B.nd u1 r1 c1) == .nil) = true then (BT.D u .zero)
              else if (u ≤ w || !(r == .nil) || headLvl (B.nd u1 r1 c1) ≤ u) = true
                   then BT.D u (bArg u (B.nd u1 r1 c1))
              else bClose u (bFold u (B.nd u1 r1 c1))) = _
        rw [if_neg (show ¬ (((B.nd u1 r1 c1) == (.nil : B)) = true) from by
          intro hc; exact B.noConfusion (of_decide_eq_true hc)), if_neg htest]
      rw [hK]
      cases hst : (bFold u (B.nd u1 r1 c1)).2 with
      | none =>
        rw [bClose_none' u _ hst]
        obtain ⟨hne1, hh⟩ := h2 u hst (by intro hc; exact B.noConfusion hc)
        refine ⟨hne1, ?_⟩
        intro z hz
        obtain ⟨s, a, hza, hus⟩ := hh z hz
        exact ⟨s, a, hza, by omega⟩
      | some a =>
        rw [bClose_some' u _ a hst]
        have hA : AtomsL ((bFold u (B.nd u1 r1 c1)).1) :=
          (atomsL_bArg_bFold (B.nd u1 r1 c1) u).2
        have htoL : (bplus ((bFold u (B.nd u1 r1 c1)).1) (BT.D u a)).toL
            = ((bFold u (B.nd u1 r1 c1)).1).toL ++ [BT.D u a] :=
          toL_bplus _ _ hA (atomsL_D u a)
        rw [htoL]
        refine ⟨?_, ?_⟩
        · intro hc
          exact absurd (List.append_eq_nil_iff.mp hc).2 (List.cons_ne_nil _ _)
        · intro z hz
          rw [getLast?_append_right _ _ (List.cons_ne_nil (BT.D u a) [])] at hz
          have hz' : (some (BT.D u a) : Option BT) = some z := hz
          exact ⟨u, a, (Option.some.inj hz').symm, Nat.le_refl u⟩

/-! ### 14. `mkC2` を評価する -/

/-- `mkC2` の `t34`。 -/
def t34B (M : Trans.Recal.PS) (j0 : Int) (t2 : BT) : BT × BT :=
  match (t2.toL.getLast?).getD BT.zero with
  | .D s inner => if ((s : Nat) : Int) == gp1 M j0 then (BT.ofL t2.toL.dropLast, inner)
                  else (t2, t2)
  | _ => (t2, t2)

theorem mkC2_D (M : Trans.Recal.PS) (j0 j1 : Int) (ty v : Nat) (t2 : BT) :
    mkC2 M j0 j1 ty (BT.D v t2)
      = (if (ty == 1 || ty == 3 || ty == 5) = true then
           BT.D v (bplus t2 (BT.D (gp1 M j1).toNat BT.zero))
         else if (ty == 2 || ty == 4) = true then
           (if (t2 == BT.zero) = true then
              BT.D v (BT.D (gp1 M j0).toNat (BT.D (gp1 M j1).toNat BT.zero))
            else
              BT.D v (bplus (t34B M j0 t2).1 (BT.D (gp1 M j0).toNat
                (bplus (t34B M j0 t2).2 (BT.D (gp1 M j1).toNat BT.zero)))))
         else BT.D v (BT.D (gp1 M j1).toNat BT.zero)) := rfl

theorem toNat_cast (n : Nat) : (((n : Nat) : Int)).toNat = n := rfl

theorem getLast?_ne_nil {α : Type _} : ∀ (l : List α), l ≠ [] → ∃ z, l.getLast? = some z := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a tl ih =>
    intro _
    cases tl with
    | nil => exact ⟨a, rfl⟩
    | cons b r =>
      obtain ⟨z, hz⟩ := ih (List.cons_ne_nil b r)
      exact ⟨z, by rw [getLast?_cons_of_ne_nil a (b :: r) (List.cons_ne_nil b r)]; exact hz⟩

theorem mkC2_135 (M : Trans.Recal.PS) (j0 j1 : Int) (ty v : Nat) (t2 : BT)
    (h1 : (ty == 1 || ty == 3 || ty == 5) = true) :
    mkC2 M j0 j1 ty (BT.D v t2) = BT.D v (bplus t2 (BT.D (gp1 M j1).toNat BT.zero)) := by
  rw [mkC2_D, if_pos h1]

theorem mkC2_6 (M : Trans.Recal.PS) (j0 j1 : Int) (ty v : Nat) (t2 : BT)
    (h1 : (ty == 1 || ty == 3 || ty == 5) = false) (h2 : (ty == 2 || ty == 4) = false) :
    mkC2 M j0 j1 ty (BT.D v t2) = BT.D v (BT.D (gp1 M j1).toNat BT.zero) := by
  rw [mkC2_D, if_neg (by rw [h1]; exact Bool.noConfusion),
    if_neg (by rw [h2]; exact Bool.noConfusion)]

/-- `t2` の末尾が `psi_p(aa)` のとき: `t34` は最後の成分をはがす。 -/
theorem mkC2_24_split (M : Trans.Recal.PS) (j0 j1 : Int) (ty v pp : Nat) (A aa : BT)
    (h1 : (ty == 1 || ty == 3 || ty == 5) = false) (h2 : (ty == 2 || ty == 4) = true)
    (hA : AtomsL A) (hnfA : NfSum A) (hgp : gp1 M j0 = ((pp : Nat) : Int)) :
    mkC2 M j0 j1 ty (BT.D v (bplus A (BT.D pp aa)))
      = BT.D v (bplus A (BT.D pp (bplus aa (BT.D (gp1 M j1).toNat BT.zero)))) := by
  have htoL : (bplus A (BT.D pp aa)).toL = A.toL ++ [BT.D pp aa] :=
    toL_bplus A (BT.D pp aa) hA (atomsL_D pp aa)
  have hnz : ((bplus A (BT.D pp aa)) == BT.zero) = false := by
    refine bt_beq_false _ _ ?_
    intro hc
    have hz : (bplus A (BT.D pp aa)).toL = [] := by rw [hc]; rfl
    rw [htoL] at hz
    exact absurd (List.append_eq_nil_iff.mp hz).2 (List.cons_ne_nil _ _)
  have ht34 : t34B M j0 (bplus A (BT.D pp aa)) = (A, aa) := by
    show (match ((bplus A (BT.D pp aa)).toL.getLast?).getD BT.zero with
          | .D s inner => if ((s : Nat) : Int) == gp1 M j0
                          then (BT.ofL ((bplus A (BT.D pp aa)).toL.dropLast), inner)
                          else (bplus A (BT.D pp aa), bplus A (BT.D pp aa))
          | _ => (bplus A (BT.D pp aa), bplus A (BT.D pp aa))) = _
    rw [htoL, List.getLast?_concat]
    show (if ((pp : Nat) : Int) == gp1 M j0
          then (BT.ofL ((A.toL ++ [BT.D pp aa]).dropLast), aa)
          else (BT.ofL (A.toL ++ [BT.D pp aa]), BT.ofL (A.toL ++ [BT.D pp aa]))) = _
    rw [if_pos (by rw [hgp]; exact beqI_self _), List.dropLast_concat, hnfA]
  rw [mkC2_D, if_neg (by rw [h1]; exact Bool.noConfusion), if_pos h2,
    if_neg (by rw [hnz]; exact Bool.noConfusion), ht34, hgp, toNat_cast]

/-- `t2` の末尾の頭が `p` でないとき: `t34` は `t2` をそのまま二度使う。 -/
theorem mkC2_24_keep (M : Trans.Recal.PS) (j0 j1 : Int) (ty v pp : Nat) (t2 : BT)
    (h1 : (ty == 1 || ty == 3 || ty == 5) = false) (h2 : (ty == 2 || ty == 4) = true)
    (hne : t2.toL ≠ []) (hgp : gp1 M j0 = ((pp : Nat) : Int))
    (hhd : ∀ z, t2.toL.getLast? = some z → ∃ s a, z = BT.D s a ∧ pp < s) :
    mkC2 M j0 j1 ty (BT.D v t2)
      = BT.D v (bplus t2 (BT.D pp (bplus t2 (BT.D (gp1 M j1).toNat BT.zero)))) := by
  obtain ⟨z, hz⟩ := getLast?_ne_nil t2.toL hne
  obtain ⟨s, a, hza, hps⟩ := hhd z hz
  have hnz : (t2 == BT.zero) = false := by
    refine bt_beq_false _ _ ?_
    intro hc
    have hzz : t2.toL = [] := by rw [hc]; rfl
    exact hne hzz
  have ht34 : t34B M j0 t2 = (t2, t2) := by
    show (match (t2.toL.getLast?).getD BT.zero with
          | .D s inner => if ((s : Nat) : Int) == gp1 M j0
                          then (BT.ofL t2.toL.dropLast, inner) else (t2, t2)
          | _ => (t2, t2)) = _
    rw [hz]
    show (match z with
          | .D s inner => if ((s : Nat) : Int) == gp1 M j0
                          then (BT.ofL t2.toL.dropLast, inner) else (t2, t2)
          | _ => (t2, t2)) = _
    rw [hza]
    show (if ((s : Nat) : Int) == gp1 M j0 then (BT.ofL t2.toL.dropLast, a) else (t2, t2)) = _
    rw [if_neg (by
      rw [hgp]
      refine (by
        intro hcc
        exact absurd (of_decide_eq_true hcc) (by omega)))]
  rw [mkC2_D, if_neg (by rw [h1]; exact Bool.noConfusion), if_pos h2,
    if_neg (by rw [hnz]; exact Bool.noConfusion), ht34, hgp, toNat_cast]

/-! ### 15. 糊: `mkC2` は `t` の側で同じ節の寄与を計算する -/

theorem admB_of_adm (t : B) (j : Nat) (h : isAdmB t j = true) : admB t j = j := by
  cases j with
  | zero => rfl
  | succ k => rw [admB_succ, if_pos h]

theorem admB_lt_of_not_adm (t : B) (j : Nat) (h : isAdmB t j = false) : admB t j < j := by
  cases j with
  | zero =>
    rw [isAdmB_zero t] at h
    exact absurd h (by intro hc; exact Bool.noConfusion hc)
  | succ k =>
    rw [admB_succ, if_neg (by rw [h]; exact Bool.noConfusion)]
    have := admB_le t k
    omega

theorem tyMainB_def (t : B) (j0 j1 : Nat) :
    tyMainB t j0 j1
      = (if entL t j1 == 0 then (if isAdmB t j0 then 1 else 2)
         else if entL t j1 ≤ entL t j0 then (if isAdmB t j0 then 3 else 4)
         else if j0 + 1 < j1 then 5 else 6) := rfl

/-- **項目 2**、底のデータを名前で受け取った形。 -/
theorem mkC2_glue_aux (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) (hz : bVal (dropLastB t) ≠ BT.zero)
    (p uu : Nat) (rL : B) (hbot : botOf 0 t = (p, uu, rL)) :
    mkC2 (psM (matB t 0)) ((j0B t : Nat) : Int) ((sizeB t - 1 : Nat) : Int)
        (tyMainB t (j0B t) (sizeB t - 1)) (bMark (dropLastB t) (admB t (j0B t)))
      = bMark t (admB t (j0B t)) := by
  have hP : (botOf 0 t).1 = p := by rw [hbot]
  have hU : (botOf 0 t).2.1 = uu := by rw [hbot]
  have hR : (botOf 0 t).2.2 = rL := by rw [hbot]
  have hne : t ≠ .nil := ne_nil_of_size t h1
  obtain ⟨w', v, r, c, hq, hMt, hMs, hEq, hLt⟩ := markPair t hnf h1 hprin hz
  rw [hP, hU, hR] at hEq hLt
  obtain ⟨⟨ww, rr, hnode0⟩, hposrel⟩ := botSpine t 0 (j0B t) (lastSpine_dropLast_ne t h1 hprin)
  rw [hP, hU, hR] at hnode0
  rw [hR] at hposrel
  have hpj0 : entL t (j0B t) = p := entL_nodeAtB t 0 (j0B t) 0 _ hnode0
  have huuj1 : entL t (sizeB t - 1) = uu := by
    rw [← hU]
    exact entL_nodeAtB t 0 (sizeB t - 1) 0 _ (nodeAtB_last t 0 hne)
  have hgp1 : gp1 (psM (matB t 0)) ((sizeB t - 1 : Nat) : Int) = ((uu : Nat) : Int) := by
    rw [psM_gp1 (matB t 0) (sizeB t - 1)]
    show ((entL t (sizeB t - 1) : Nat) : Int) = _
    rw [huuj1]
  have hgp0 : gp1 (psM (matB t 0)) ((j0B t : Nat) : Int) = ((p : Nat) : Int) := by
    rw [psM_gp1 (matB t 0) (j0B t)]
    show ((entL t (j0B t) : Nat) : Int) = _
    rw [hpj0]
  have hty : tyMainB t (j0B t) (sizeB t - 1)
      = (if uu == 0 then (if isAdmB t (j0B t) then 1 else 2)
         else if uu ≤ p then (if isAdmB t (j0B t) then 3 else 4)
         else if j0B t + 1 < sizeB t - 1 then 5 else 6) := by
    rw [tyMainB_def, huuj1, hpj0]
  by_cases hadm0 : isAdmB t (j0B t) = true
  · obtain ⟨hc, hv⟩ := hEq (admB_of_adm t (j0B t) hadm0)
    have hTfin : bArg v c = bplus (bArg v rL) (BT.D uu BT.zero) := by
      rw [hc, bArg_nd, bK_nil]
    have hSfin : bArg v (dropLastB c) = bArg v rL := by
      rw [hc]
      rfl
    rw [hMt, hMs, hTfin, hSfin]
    by_cases hu0 : (uu == 0) = true
    · rw [show tyMainB t (j0B t) (sizeB t - 1) = 1 from by rw [hty, if_pos hu0, if_pos hadm0],
        mkC2_135 _ _ _ 1 v _ rfl, hgp1, toNat_cast]
    · by_cases hle : uu ≤ p
      · rw [show tyMainB t (j0B t) (sizeB t - 1) = 3 from by
            rw [hty, if_neg hu0, if_pos hle, if_pos hadm0],
          mkC2_135 _ _ _ 3 v _ rfl, hgp1, toNat_cast]
      · by_cases hlt : j0B t + 1 < sizeB t - 1
        · rw [show tyMainB t (j0B t) (sizeB t - 1) = 5 from by
              rw [hty, if_neg hu0, if_neg hle, if_pos hlt],
            mkC2_135 _ _ _ 5 v _ rfl, hgp1, toNat_cast]
        · have hrLn : rL = .nil := sizeB_eq_zero rL (by omega)
          rw [show tyMainB t (j0B t) (sizeB t - 1) = 6 from by
              rw [hty, if_neg hu0, if_neg hle, if_neg hlt],
            mkC2_6 _ _ _ 6 v _ rfl rfl, hgp1, toNat_cast, hrLn]
          show BT.D v (BT.D uu BT.zero) = BT.D v (bplus (bArg v (.nil : B)) (BT.D uu BT.zero))
          rw [show bArg v (.nil : B) = BT.zero from rfl,
            bplus_zero_left _ (nfSum_D uu BT.zero)]
  · have hadm0' : isAdmB t (j0B t) = false := by
      cases hb : isAdmB t (j0B t) with
      | true => exact absurd hb hadm0
      | false => rfl
    obtain ⟨hT, hS⟩ := hLt (admB_lt_of_not_adm t (j0B t) hadm0')
    have hj0pos : 1 ≤ j0B t := pos_of_not_adm t (j0B t) hadm0'
    have hcoll0 := coll_of_not_adm' t (j0B t) ww p rr (B.nd uu rL .nil) hj0pos hnode0 hadm0'
    obtain ⟨_, hwwp, _, hhl⟩ := collB_parts ww p rr (B.nd uu rL .nil) hcoll0
    by_cases hrL : rL = .nil
    · subst hrL
      have hpu : p < uu := by
        rw [headLvl_nd_nil] at hhl
        exact hhl
      have hTfin : bArg v c = BT.D uu BT.zero := by
        rw [hT, bot_append p uu .nil hpu,
          show bClose p (bFold p (.nil : B)) = BT.zero from rfl]
        exact bplus_zero_left _ (nfSum_D uu BT.zero)
      have hSfin : bArg v (dropLastB c) = BT.D p BT.zero := by
        rw [hS, if_pos (show ((.nil : B) == (.nil : B)) = true from rfl)]
      rw [hMt, hMs, hTfin, hSfin,
        show tyMainB t (j0B t) (sizeB t - 1) = 6 from by
          rw [hty, if_neg (show ¬ ((uu == 0) = true) from by
              intro hcc; exact absurd (of_decide_eq_true hcc) (by omega)),
            if_neg (show ¬ (uu ≤ p) from by omega),
            if_neg (show ¬ (j0B t + 1 < sizeB t - 1) from by
              have hz0 : sizeB (.nil : B) = 0 := rfl
              omega)],
        mkC2_6 _ _ _ 6 v _ rfl rfl, hgp1, toNat_cast]
    · have hhl2 : p < headLvl rL := by
        rw [headLvl_nd_ne uu rL .nil hrL] at hhl
        exact hhl
      have hrpos : 0 < sizeB rL := sizeB_pos rL hrL
      have hSfin : bArg v (dropLastB c) = bClose p (bFold p rL) := by
        rw [hS, if_neg (by rw [beqB_false rL .nil hrL]; exact Bool.noConfusion)]
      by_cases hpu : p < uu
      · have hTfin : bArg v c = bplus (bClose p (bFold p rL)) (BT.D uu BT.zero) := by
          rw [hT, bot_append p uu rL hpu]
        rw [hMt, hMs, hTfin, hSfin,
          show tyMainB t (j0B t) (sizeB t - 1) = 5 from by
            rw [hty, if_neg (show ¬ ((uu == 0) = true) from by
                intro hcc; exact absurd (of_decide_eq_true hcc) (by omega)),
              if_neg (show ¬ (uu ≤ p) from by omega),
              if_pos (show j0B t + 1 < sizeB t - 1 from by omega)],
          mkC2_135 _ _ _ 5 v _ rfl, hgp1, toNat_cast]
      · have hty24 : tyMainB t (j0B t) (sizeB t - 1) = 2
            ∨ tyMainB t (j0B t) (sizeB t - 1) = 4 := by
          by_cases hu0 : (uu == 0) = true
          · exact Or.inl (by rw [hty, if_pos hu0, if_neg hadm0])
          · exact Or.inr (by rw [hty, if_neg hu0, if_pos (show uu ≤ p from by omega),
              if_neg hadm0])
        have hb1 : ((tyMainB t (j0B t) (sizeB t - 1) == 1)
            || (tyMainB t (j0B t) (sizeB t - 1) == 3)
            || (tyMainB t (j0B t) (sizeB t - 1) == 5)) = false := by
          rcases hty24 with h | h <;> rw [h] <;> rfl
        have hb2 : ((tyMainB t (j0B t) (sizeB t - 1) == 2)
            || (tyMainB t (j0B t) (sizeB t - 1) == 4)) = true := by
          rcases hty24 with h | h <;> rw [h] <;> rfl
        cases hst : (bFold p rL).2 with
        | none =>
          obtain ⟨hTn, hSn⟩ := bot_none p uu rL hpu hst
          have hTfin : bArg v c
              = bplus (bFold p rL).1 (BT.D p (bplus (bFold p rL).1 (BT.D uu BT.zero))) := by
            rw [hT, hTn]
          have hSfin' : bArg v (dropLastB c) = (bFold p rL).1 := by rw [hSfin, hSn]
          obtain ⟨hne1, hhd⟩ := (lastAtom_aux rL).2 p hst hrL
          rw [hMt, hMs, hTfin, hSfin',
            mkC2_24_keep _ _ _ _ v p _ hb1 hb2 hne1 hgp0 hhd, hgp1, toNat_cast]
        | some a =>
          obtain ⟨hTs, hSs⟩ := bot_some p uu rL a hpu hst
          have hTfin : bArg v c
              = bplus (bFold p rL).1 (BT.D p (bplus a (BT.D uu BT.zero))) := by
            rw [hT, hTs]
          have hSfin' : bArg v (dropLastB c) = bplus (bFold p rL).1 (BT.D p a) := by
            rw [hSfin, hSs]
          rw [hMt, hMs, hTfin, hSfin',
            mkC2_24_split _ _ _ _ v p _ a hb1 hb2 (atomsL_bArg_bFold rL p).2
              (nfSum_bFold_bClose rL p).1 hgp0, hgp1, toNat_cast]

/-- **項目 2。** `mkC2` は `t` の側で同じ節の寄与を計算する。 -/
theorem mkC2_glue (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) (hz : bVal (dropLastB t) ≠ BT.zero) :
    mkC2 (psM (matB t 0)) ((j0B t : Nat) : Int) ((sizeB t - 1 : Nat) : Int)
        (tyMainB t (j0B t) (sizeB t - 1)) (bMark (dropLastB t) (admB t (j0B t)))
      = bMark t (admB t (j0B t)) :=
  mkC2_glue_aux t hnf h1 hprin hz (botOf 0 t).1 (botOf 0 t).2.1 (botOf 0 t).2.2 rfl

/-! ### 16. 枝の材料を木の言葉に直す -/

theorem lenI_ne_one (t : B) (h1 : 1 < sizeB t) :
    (lenI (psM (matB t 0)) - 1 == 0) = false := by
  rw [lenI_matB]
  exact decide_eq_false (by omega)

theorem mainC1_tree (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) (g : Nat) (tbl : Trans.Recal.Memo) :
    mainC1 g (psM (matB t 0)) tbl
      = (Trans.Recal.runAux g (psM (matB (dropLastB t) 0))
           (some ((admB t (j0B t) : Nat) : Int))).run
          ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tbl).2 := by
  show (Trans.Recal.runAux g (predP (psM (matB t 0)))
      (some (adm (psM (matB t 0))
        (fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0)))).run
      ((Trans.Recal.runAux g (predP (psM (matB t 0))) none).run tbl).2 = _
  rw [branch_jn1 t h1 hprin, predP_matB t h1]

theorem mainC2_tree (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) (c1 : BT) :
    mainC2 (psM (matB t 0)) c1
      = mkC2 (psM (matB t 0)) ((j0B t : Nat) : Int) ((sizeB t - 1 : Nat) : Int)
          (tyMainB t (j0B t) (sizeB t - 1)) c1 := by
  show mkC2 (psM (matB t 0)) (fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0)
      (lenI (psM (matB t 0)) - 1)
      (transTypeMain (psM (matB t 0)) (fpar (psM (matB t 0)) 0 (lenI (psM (matB t 0)) - 1) 0)
        (lenI (psM (matB t 0)) - 1)) c1 = _
  rw [branch_ty t h1 hprin, fpar_last_spine t h1 hprin, lenI_sub_one t h1]

/-! ### 17. 型 1-6 の枝、`Trans` の側 -/

/-- **`runAux` の型 1-6 の枝** (要求は `Trans`)。 -/
theorem runAux_main (g : Nat) (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true)
    (hzv : bVal (dropLastB t) ≠ BT.zero)
    (tbl : Trans.Recal.Memo) (hs : SoundB tbl)
    (ih : ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tb).1
            = bVal (dropLastB t)
          ∧ SoundB ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tb).2)
    (ihm : ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0))
             (some ((admB t (j0B t) : Nat) : Int))).run tb).1
            = bMark (dropLastB t) (admB t (j0B t))
          ∧ SoundB ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0))
             (some ((admB t (j0B t) : Nat) : Int))).run tb).2) :
    ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) none).run tbl).1 = bVal t
      ∧ SoundB ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) none).run tbl).2 := by
  cases hf : tbl.find? (fun z => z.1 == (psM (matB t 0), (none : Option Int))) with
  | some pp =>
    rw [runHit g _ none tbl pp hf]
    obtain ⟨hg, he⟩ := goodB_of_find hs hf
    exact ⟨hg t none hnf he (Or.inl rfl), hs⟩
  | none =>
    obtain ⟨hv0, hsd0⟩ := ih tbl hs
    have ht1 : ((Trans.Recal.runAux g (predP (psM (matB t 0))) none).run tbl).1
        = bVal (dropLastB t) := by
      rw [predP_matB t h1]
      exact hv0
    have hne0 : (bVal (dropLastB t) == BT.zero) = false := bt_beq_false _ _ hzv
    have hc1 : (mainC1 g (psM (matB t 0)) tbl).1 = bMark (dropLastB t) (admB t (j0B t)) := by
      rw [mainC1_tree t h1 hprin]
      exact (ihm _ hsd0).1
    have hsd1 : SoundB (mainC1 g (psM (matB t 0)) tbl).2 := by
      rw [mainC1_tree t h1 hprin]
      exact (ihm _ hsd0).2
    have hc2 : mainC2 (psM (matB t 0)) (mainC1 g (psM (matB t 0)) tbl).1
        = bMark t (admB t (j0B t)) := by
      rw [mainC2_tree t h1 hprin, hc1]
      exact mkC2_glue t hnf h1 hprin hzv
    obtain ⟨hoks, hokt⟩ := markOKB_admB_j0 t hnf h1 hprin hzv
    have hval : mainVal (psM (matB t 0)) (bVal (dropLastB t))
        (mainC1 g (psM (matB t 0)) tbl).1 = bVal t := by
      show (replMark (Trans.Dict.BT.size (bVal (dropLastB t))
              + mainDep (mainC1 g (psM (matB t 0)) tbl).1
                  (mainC2 (psM (matB t 0)) (mainC1 g (psM (matB t 0)) tbl).1))
            (bVal (dropLastB t)) (mainC1 g (psM (matB t 0)) tbl).1
            (mainC2 (psM (matB t 0)) (mainC1 g (psM (matB t 0)) tbl).1)).getD BT.zero = _
      rw [hc2, hc1,
        subst_bVal' t (admB t (j0B t)) hnf h1 hoks hokt _ (by
          show BT.size (bVal (dropLastB t)) + BT.size (bMark (dropLastB t) (admB t (j0B t)))
              + BT.size (bMark t (admB t (j0B t))) + 4
            ≤ BT.size (bVal (dropLastB t))
              + (BT.size (bMark (dropLastB t) (admB t (j0B t)))
                + BT.size (bMark t (admB t (j0B t))) + 4)
          omega)]
      rfl
    rw [run_main_miss_none g (psM (matB t 0)) tbl (bVal (dropLastB t))
      (isReducedP_matB t hnf) (lenI_ne_one t h1) hprin ht1 hne0 hf]
    refine ⟨hval, ?_⟩
    show SoundB (((psM (matB t 0), (none : Option Int)),
      mainVal (psM (matB t 0)) (bVal (dropLastB t)) (mainC1 g (psM (matB t 0)) tbl).1)
        :: (mainC1 g (psM (matB t 0)) tbl).2)
    rw [hval]
    exact SoundB_cons hsd1 (goodB_mk t none)

/-! ### 18. 「寄与が 1 つの `D`」は最後の節を落としても残る -/

theorem append_eq_single {α : Type _} : ∀ (l1 l2 : List α) (x : α), l1 ++ l2 = [x] → l2 ≠ [] →
    l1 = [] ∧ l2 = [x] := by
  intro l1
  cases l1 with
  | nil => intro l2 x h _; exact ⟨rfl, h⟩
  | cons a rest =>
    intro l2 x h hne
    exfalso
    have h' : a :: (rest ++ l2) = [x] := h
    have h2 : rest ++ l2 = [] := List.tail_eq_of_cons_eq h'
    exact hne (List.append_eq_nil_iff.mp h2).2

theorem bplus_D_split (A Bb : BT) (hA : AtomsL A) (hB : AtomsL Bb)
    (hnfA : NfSum A) (hnfB : NfSum Bb) (hBne : Bb.toL ≠ []) (p : Nat) (a : BT)
    (h : bplus A Bb = BT.D p a) : A = BT.zero ∧ Bb = BT.D p a := by
  have htoL : A.toL ++ Bb.toL = [BT.D p a] := by
    rw [← toL_bplus A Bb hA hB, h]
    rfl
  obtain ⟨h1, h2⟩ := append_eq_single A.toL Bb.toL (BT.D p a) htoL hBne
  constructor
  · have : BT.ofL A.toL = A := hnfA
    rw [h1] at this
    exact this.symm
  · have : BT.ofL Bb.toL = Bb := hnfB
    rw [h2] at this
    exact this.symm

/-- 空でない添字の畳み込みは 0 にならない。 -/
theorem bClose_bFold_ne_zero : ∀ (x : B) (w : Nat), x ≠ .nil → bClose w (bFold w x) ≠ BT.zero := by
  intro x
  cases x with
  | nil => intro w h; exact absurd rfl h
  | nd u1 r1 c1 =>
    intro w _
    by_cases hw : w < u1
    · rw [bClose_bFold_nd_lt w u1 r1 c1 hw]
      intro hc
      have htoL : (bplus (bClose w (bFold w r1)) (bK w u1 r1 c1)).toL
          = (bClose w (bFold w r1)).toL ++ (bK w u1 r1 c1).toL :=
        toL_bplus _ _ (atomsL_bClose w (bFold w r1) (atomsL_bArg_bFold r1 w).2)
          (atomsL_bK w u1 r1 c1)
      have hz : (bplus (bClose w (bFold w r1)) (bK w u1 r1 c1)).toL = [] := by
        rw [hc]; rfl
      rw [htoL] at hz
      exact (lastAtom_aux c1).1 w u1 r1 |>.1 (List.append_eq_nil_iff.mp hz).2
    · cases hst : (bFold w r1).2 with
      | none =>
        rw [bClose_bFold_nd_none w u1 r1 c1 hw hst]
        intro hc
        have htoL : (bplus (bFold w r1).1 (BT.D w (bplus (bFold w r1).1 (bK w u1 r1 c1)))).toL
            = ((bFold w r1).1).toL ++ [BT.D w (bplus (bFold w r1).1 (bK w u1 r1 c1))] :=
          toL_bplus _ _ (atomsL_bArg_bFold r1 w).2 (atomsL_D _ _)
        have hz : (bplus (bFold w r1).1
            (BT.D w (bplus (bFold w r1).1 (bK w u1 r1 c1)))).toL = [] := by
          rw [hc]; rfl
        rw [htoL] at hz
        exact absurd (List.append_eq_nil_iff.mp hz).2 (List.cons_ne_nil _ _)
      | some a =>
        rw [bClose_bFold_nd_some w u1 r1 c1 hw a hst]
        intro hc
        have htoL : (bplus (bFold w r1).1 (BT.D w (bplus a (bK w u1 r1 c1)))).toL
            = ((bFold w r1).1).toL ++ [BT.D w (bplus a (bK w u1 r1 c1))] :=
          toL_bplus _ _ (atomsL_bArg_bFold r1 w).2 (atomsL_D _ _)
        have hz : (bplus (bFold w r1).1 (BT.D w (bplus a (bK w u1 r1 c1)))).toL = [] := by
          rw [hc]; rfl
        rw [htoL] at hz
        exact absurd (List.append_eq_nil_iff.mp hz).2 (List.cons_ne_nil _ _)

/-- 先頭の段が親より高いなら、畳み込みの第 1 成分は 0 でない。 -/
theorem bFold_fst_ne_zero : ∀ (x : B) (w : Nat), x ≠ .nil → w < headLvl x →
    (bFold w x).1 ≠ BT.zero := by
  intro x
  induction x with
  | nil => intro w h _; exact absurd rfl h
  | nd u1 r1 c1 ihr _ =>
    intro w _ hh
    by_cases hw : w < u1
    · have h1 : (bFold w (B.nd u1 r1 c1)).1
          = bplus (bClose w (bFold w r1)) (bK w u1 r1 c1) := by
        rw [bFold_nd_lt w u1 r1 c1 hw]
      rw [h1]
      intro hc
      have htoL : (bplus (bClose w (bFold w r1)) (bK w u1 r1 c1)).toL
          = (bClose w (bFold w r1)).toL ++ (bK w u1 r1 c1).toL :=
        toL_bplus _ _ (atomsL_bClose w (bFold w r1) (atomsL_bArg_bFold r1 w).2)
          (atomsL_bK w u1 r1 c1)
      have hz : (bplus (bClose w (bFold w r1)) (bK w u1 r1 c1)).toL = [] := by
        rw [hc]; rfl
      rw [htoL] at hz
      exact (lastAtom_aux c1).1 w u1 r1 |>.1 (List.append_eq_nil_iff.mp hz).2
    · have hr1 : r1 ≠ .nil := by
        intro hc
        rw [hc, headLvl_nd_nil] at hh
        omega
      have hhr : w < headLvl r1 := by
        rw [headLvl_nd_ne u1 r1 c1 hr1] at hh
        exact hh
      have h1 : (bFold w (B.nd u1 r1 c1)).1 = (bFold w r1).1 := by
        cases hst : (bFold w r1).2 with
        | none => rw [bFold_nd_ge w u1 r1 c1 hw, hst]
        | some a => rw [bFold_nd_ge w u1 r1 c1 hw, hst]
      rw [h1]
      exact ihr w hr1 hhr

/-- **(R')** 寄与が 1 つの `D` なら、最後の節を落としても 1 つの `D`。 -/
theorem bK_dropLast_D : ∀ (c : B) (w u : Nat) (r : B),
    (∃ p a, bK w u r c = BT.D p a) → (∃ p a, bK w u r (dropLastB c) = BT.D p a) := by
  intro c
  induction c with
  | nil => intro w u r h; exact h
  | nd u1 r1 c1 _ ihc =>
    intro w u r h
    by_cases hcoll : collB w u r (B.nd u1 r1 c1) = true
    · obtain ⟨hcn, hwu, hrn, hhl⟩ := collB_parts w u r (B.nd u1 r1 c1) hcoll
      -- 潰れているなら、子はひとりっ子で段が上がる
      have hr1 : r1 = .nil := by
        by_cases hc : r1 = .nil
        · exact hc
        · exfalso
          have hhr : u < headLvl r1 := by
            rw [headLvl_nd_ne u1 r1 c1 hc] at hhl
            exact hhl
          have hwu1 : ¬ (u < u1) := by
            intro hlt
            rw [bK_coll w u r (B.nd u1 r1 c1) hcoll, bClose_bFold_nd_lt u u1 r1 c1 hlt] at h
            obtain ⟨p, a, hpa⟩ := h
            obtain ⟨hzz, _⟩ := bplus_D_split _ _
              (atomsL_bClose u (bFold u r1) (atomsL_bArg_bFold r1 u).2) (atomsL_bK u u1 r1 c1)
              (nfSum_bFold_bClose r1 u).2 (nfSum_bK u u1 r1 c1)
              ((lastAtom_aux c1).1 u u1 r1).1 p a hpa
            exact bClose_bFold_ne_zero r1 u hc hzz
          rw [bK_coll w u r (B.nd u1 r1 c1) hcoll] at h
          obtain ⟨p, a, hpa⟩ := h
          cases hst : (bFold u r1).2 with
          | none =>
            rw [bClose_bFold_nd_none u u1 r1 c1 hwu1 hst] at hpa
            obtain ⟨hzz, _⟩ := bplus_D_split _ _ (atomsL_bArg_bFold r1 u).2 (atomsL_D _ _)
              (nfSum_bFold_bClose r1 u).1 (nfSum_D _ _) (List.cons_ne_nil _ _) p a hpa
            exact bFold_fst_ne_zero r1 u hc hhr hzz
          | some aa =>
            rw [bClose_bFold_nd_some u u1 r1 c1 hwu1 aa hst] at hpa
            obtain ⟨hzz, _⟩ := bplus_D_split _ _ (atomsL_bArg_bFold r1 u).2 (atomsL_D _ _)
              (nfSum_bFold_bClose r1 u).1 (nfSum_D _ _) (List.cons_ne_nil _ _) p a hpa
            exact bFold_fst_ne_zero r1 u hc hhr hzz
      subst hr1
      have hu1 : u < u1 := by
        rw [headLvl_nd_nil] at hhl
        exact hhl
      cases hc1 : c1 with
      | nil =>
        exact ⟨u, BT.zero, by
          show bK w u r (dropLastB (B.nd u1 .nil .nil)) = _
          rw [show dropLastB (B.nd u1 (.nil : B) (.nil : B)) = .nil from rfl, bK_nil]⟩
      | nd u2 b2 d2 =>
        subst hc1
        have hcne : (B.nd u2 b2 d2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
        have hdrop : dropLastB (B.nd u1 .nil (B.nd u2 b2 d2))
            = B.nd u1 .nil (dropLastB (B.nd u2 b2 d2)) :=
          dropLastB_nd_ne u1 .nil (B.nd u2 b2 d2) hcne
        have hcoll2 : collB w u r (B.nd u1 .nil (dropLastB (B.nd u2 b2 d2))) = true :=
          collB_mk w u r _ (by intro hcc; exact B.noConfusion hcc) hwu hrn
            (by rw [headLvl_nd_nil]; exact hu1)
        rw [hdrop, bK_coll w u r _ hcoll2, bClose_bFold_single u u1 _ hu1]
        refine ihc u u1 .nil ?_
        rw [bK_coll w u r _ hcoll, bClose_bFold_single u u1 _ hu1] at h
        exact h
    · have hcf : collB w u r (B.nd u1 r1 c1) = false := by
        cases hb : collB w u r (B.nd u1 r1 c1) with
        | true => exact absurd hb hcoll
        | false => rfl
      by_cases hdn : dropLastB (B.nd u1 r1 c1) = .nil
      · exact ⟨u, BT.zero, by rw [hdn, bK_nil]⟩
      · have hhead : headLvl (dropLastB (B.nd u1 r1 c1)) = headLvl (B.nd u1 r1 c1) :=
          headLvl_dropLast (B.nd u1 r1 c1) hdn
        have hcf2 : collB w u r (dropLastB (B.nd u1 r1 c1)) = false := by
          cases hb : collB w u r (dropLastB (B.nd u1 r1 c1)) with
          | false => rfl
          | true =>
            exfalso
            obtain ⟨_, hwu, hrn, hhl⟩ := collB_parts w u r _ hb
            rw [hhead] at hhl
            rw [collB_mk w u r (B.nd u1 r1 c1)
              (by intro hcc; exact B.noConfusion hcc) hwu hrn hhl] at hcf
            exact Bool.noConfusion hcf
        exact ⟨u, bArg u (dropLastB (B.nd u1 r1 c1)), bK_eq_D_arg w u r _ hcf2⟩

/-! ### 19. `markOKB` の道具 -/

theorem markOKB_D (x : B) (m : Nat) (h : markOKB x m = true) : ∃ p a, bMark x m = BT.D p a := by
  have h2 : (match bMark x m with | .D _ _ => true | _ => false) = true :=
    ((Bool.and_eq_true _ _).mp h).2
  cases hb : bMark x m with
  | zero =>
    rw [hb] at h2
    exact absurd h2 (by intro hc; exact Bool.noConfusion hc)
  | D p a => exact ⟨p, a, rfl⟩
  | sum a b =>
    rw [hb] at h2
    exact absurd h2 (by intro hc; exact Bool.noConfusion hc)

theorem markOKB_spine (x : B) (m : Nat) (h : markOKB x m = true) : m ∈ lastSpine x :=
  of_decide_eq_true ((Bool.and_eq_true _ _).mp h).1

theorem markOKB_mk (x : B) (m : Nat) (hsp : m ∈ lastSpine x) (p : Nat) (a : BT)
    (h : bMark x m = BT.D p a) : markOKB x m = true := by
  show (decide (m ∈ lastSpine x) && (match bMark x m with | .D _ _ => true | _ => false)) = true
  rw [decide_eq_true hsp, h]
  rfl

/-- **(R')** 型 1-6 の枝で要求される印は、`s` の側でも意味を持つ。 -/
theorem markOKB_dropLast (t : B) (m : Nat) (h1 : 1 < sizeB t)
    (hsleaf : dropLastB t ≠ .nd 0 .nil .nil)
    (hok : markOKB t m = true) (hlt : m + 1 < sizeB t) :
    markOKB (dropLastB t) m = true := by
  have hne : t ≠ .nil := ne_nil_of_size t h1
  have hleaf : t ≠ .nd 0 .nil .nil := ne_leaf_of_size t h1
  have hsp : m ∈ lastSpine t := markOKB_spine t m hok
  have hspd : m ∈ (lastSpine t).dropLast :=
    mem_dropLast_of_ne_last _ _ _ (lastSpine_getLast t hne) hsp (by omega)
  have hsps : m ∈ lastSpine (dropLastB t) := lastSpine_dropLast_sub t m hspd
  obtain ⟨q, hq⟩ := nodeAtB_isSome t 0 m (by omega)
  obtain ⟨w', u, r, c⟩ := q
  have hqs : nodeAtB 0 (dropLastB t) m = some (w', u, r, dropLastB c) :=
    nodeAtB_dropLast t 0 m w' u r c hsp hlt hq
  obtain ⟨p, a, hpa⟩ := markOKB_D t m hok
  rw [bMark_bK t m w' u r c hleaf hq] at hpa
  obtain ⟨p2, a2, hpa2⟩ := bK_dropLast_D c w' u r ⟨p, a, hpa⟩
  refine markOKB_mk (dropLastB t) m hsps p2 a2 ?_
  rw [bMark_bK (dropLastB t) m w' u r (dropLastB c) hsleaf hqs]
  exact hpa2

/-- 祖先鎖の最後から 2 番目は、最後を除く要素の最大。 -/
theorem spine_dropLast_le : ∀ (x : B) (j : Nat), j ∈ (lastSpine x).dropLast → j ≤ j0B x := by
  intro x
  induction x with
  | nil =>
    intro j h
    have h' : j ∈ ([] : List Nat) := h
    cases h'
  | nd u r c _ ihc =>
    intro j h
    cases hc : c with
    | nil =>
      exfalso
      rw [hc, lastSpine_nd] at h
      have h' : j ∈ ((sizeB r :: (([] : List Nat).map (fun i => sizeB r + 1 + i))).dropLast) := h
      have h'' : j ∈ ([] : List Nat) := h'
      cases h''
    | nd u2 b2 c2 =>
      subst hc
      have hne2 : (B.nd u2 b2 c2) ≠ .nil := by intro hcc; exact B.noConfusion hcc
      have hmapne : ((lastSpine (B.nd u2 b2 c2)).map (fun i => sizeB r + 1 + i)) ≠ [] := by
        intro hcc
        exact lastSpine_ne_nil _ hne2 (List.map_eq_nil_iff.mp hcc)
      rw [lastSpine_nd, List.dropLast_cons_of_ne_nil hmapne, ← List.map_dropLast] at h
      have hj0 : j0B (B.nd u r (B.nd u2 b2 c2))
          = ((sizeB r :: (((lastSpine (B.nd u2 b2 c2)).dropLast).map
              (fun i => sizeB r + 1 + i))).getLast?).getD 0 := by
        show ((((lastSpine (B.nd u r (B.nd u2 b2 c2))).dropLast).getLast?).getD 0) = _
        rw [lastSpine_nd, List.dropLast_cons_of_ne_nil hmapne, ← List.map_dropLast]
      cases hdl : ((lastSpine (B.nd u2 b2 c2)).dropLast) with
      | nil =>
        rw [hdl] at h hj0
        have hje : j = sizeB r := by
          rcases List.mem_cons.mp h with he | hm
          · exact he
          · have : j ∈ ([] : List Nat) := hm
            cases this
        rw [hj0, hje]
        show sizeB r ≤ sizeB r
        exact Nat.le_refl _
      | cons z zs =>
        have hdlne : ((lastSpine (B.nd u2 b2 c2)).dropLast) ≠ [] := by
          rw [hdl]; exact List.cons_ne_nil _ _
        have hmne : (((lastSpine (B.nd u2 b2 c2)).dropLast).map
            (fun i => sizeB r + 1 + i)) ≠ [] := by
          intro hcc
          exact hdlne (List.map_eq_nil_iff.mp hcc)
        rw [hj0, getLast?_cons_of_ne_nil _ _ hmne, List.getLast?_map]
        have hj0c : j0B (B.nd u2 b2 c2)
            = ((((lastSpine (B.nd u2 b2 c2)).dropLast).getLast?).getD 0) := rfl
        cases hq : (((lastSpine (B.nd u2 b2 c2)).dropLast).getLast?) with
        | none =>
          exfalso
          exact hdlne (List.getLast?_eq_none_iff.mp hq)
        | some j0' =>
          have hj0c' : j0B (B.nd u2 b2 c2) = j0' := by rw [hj0c, hq]; rfl
          show j ≤ sizeB r + 1 + j0'
          rcases List.mem_cons.mp h with he | hm
          · omega
          · obtain ⟨k, hk, hke⟩ := List.mem_map.mp hm
            have := ihc k hk
            rw [hj0c'] at this
            omega

/-- `psi_p(0)` の右端の道の上に `psi_v(psi_p(0))` は無い。 -/
theorem isMarkedB_D_zero (p v : Nat) :
    isMarkedB (BT.D p BT.zero) (BT.D v (BT.D p BT.zero)) = false := by
  have hb1 : (BT.D p BT.zero == BT.D v (BT.D p BT.zero)) = false := by
    show ((p == v) && (BT.zero == BT.D p BT.zero)) = false
    rw [show (BT.zero == BT.D p BT.zero) = false from rfl, Bool.and_false]
  show isMarkedBAux (Trans.Dict.BT.size (BT.D p BT.zero) + 2) (some (BT.D p BT.zero))
    (BT.D v (BT.D p BT.zero)) = false
  show (if (BT.D p BT.zero == BT.D v (BT.D p BT.zero)) = true then true
        else isMarkedBAux 3 (nextMarkedB (BT.D p BT.zero)) (BT.D v (BT.D p BT.zero))) = false
  rw [if_neg (by rw [hb1]; exact Bool.noConfusion)]
  show (if (BT.zero == BT.D v (BT.D p BT.zero)) = true then true
        else isMarkedBAux 2 (nextMarkedB BT.zero) (BT.D v (BT.D p BT.zero))) = false
  rw [if_neg (by
    rw [show (BT.zero == BT.D v (BT.D p BT.zero)) = false from rfl]
    exact Bool.noConfusion)]
  rfl

/-! ### 20. `jn1` より下で要求される印 -/

theorem entL_last' (t : B) (hne : t ≠ .nil) : entL t (sizeB t - 1) = (botOf 0 t).2.1 :=
  entL_nodeAtB t 0 (sizeB t - 1) 0 _ (nodeAtB_last t 0 hne)

theorem gp1_last (t : B) (hne : t ≠ .nil) :
    gp1 (psM (matB t 0)) ((sizeB t - 1 : Nat) : Int) = (((botOf 0 t).2.1 : Nat) : Int) := by
  rw [psM_gp1 (matB t 0) (sizeB t - 1)]
  show ((entL t (sizeB t - 1) : Nat) : Int) = _
  rw [entL_last' t hne]

/-- **(G9)** `jn1 < k ≤ j0` で要求される印は、`t` では `psi_uu(0)`、`s` では `psi_p(0)`。 -/
theorem farMark_aux (t : B) (_hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) (hz : bVal (dropLastB t) ≠ BT.zero)
    (p uu : Nat) (rL : B) (hbot : botOf 0 t = (p, uu, rL))
    (k : Nat) (hk1 : admB t (j0B t) < k) (hk2 : k ≤ j0B t) (hok : markOKB t k = true) :
    rL = .nil ∧ bMark t k = BT.D uu BT.zero ∧ bMark (dropLastB t) k = BT.D p BT.zero := by
  have hP : (botOf 0 t).1 = p := by rw [hbot]
  have hU : (botOf 0 t).2.1 = uu := by rw [hbot]
  have hR : (botOf 0 t).2.2 = rL := by rw [hbot]
  have hne : t ≠ .nil := ne_nil_of_size t h1
  have hleaf : t ≠ .nd 0 .nil .nil := ne_leaf_of_size t h1
  have hsleaf : dropLastB t ≠ .nd 0 .nil .nil := by
    intro hc
    exact hz (by rw [hc]; exact bVal_leaf)
  obtain ⟨⟨ww, rr, hnode0⟩, hposrel⟩ := botSpine t 0 (j0B t) (lastSpine_dropLast_ne t h1 hprin)
  rw [hP, hU, hR] at hnode0
  rw [hR] at hposrel
  have hj0 : j0B t ∈ lastSpine t :=
    mem_of_mem_dropLast _ _ (j0B_mem_dropLast t h1 hprin)
  have hall : ∀ z, k ≤ z → z ≤ j0B t → isAdmB t z = false :=
    fun z hz1 hz2 => admB_not_adm t (j0B t) z (by omega) hz2
  have hspall : ∀ z, k ≤ z → z ≤ j0B t → z ∈ lastSpine t :=
    chain_spine' t (j0B t) k hj0 hall
  have hksp : k ∈ lastSpine t := hspall k (Nat.le_refl k) hk2
  have hj0lt : j0B t < sizeB t - 1 := j0B_lt t h1 hprin
  obtain ⟨q, hq⟩ := nodeAtB_isSome t 0 k (by omega)
  obtain ⟨wk, uk, rk, ck⟩ := q
  obtain ⟨tt1, tt2⟩ := tele_chain t (j0B t) p uu rL (ww, .nil) (0, rr) hnode0
    (j0B t - k) k wk uk rk ck (by omega) hq hall hspall
  have hMt : bMark t k = bClose p (bFold p (B.nd uu rL .nil)) := by
    rw [bMark_bK t k wk uk rk ck hleaf hq]
    exact tt1
  obtain ⟨qq, aa, hD⟩ := markOKB_D t k hok
  rw [hMt] at hD
  have hj0pos : 1 ≤ j0B t := pos_of_not_adm t (j0B t) (hall (j0B t) hk2 (Nat.le_refl _))
  have hcoll0 := coll_of_not_adm' t (j0B t) ww p rr (B.nd uu rL .nil) hj0pos hnode0
    (hall (j0B t) hk2 (Nat.le_refl _))
  obtain ⟨_, _, _, hhl⟩ := collB_parts ww p rr (B.nd uu rL .nil) hcoll0
  have hpu : p < uu := by
    by_cases hc : rL = .nil
    · rw [hc, headLvl_nd_nil] at hhl
      exact hhl
    · exfalso
      have hhr : p < headLvl rL := by
        rw [headLvl_nd_ne uu rL .nil hc] at hhl
        exact hhl
      have hfst : (bFold p rL).1 ≠ BT.zero := bFold_fst_ne_zero rL p hc hhr
      by_cases hpu2 : p < uu
      · rw [bot_append p uu rL hpu2] at hD
        obtain ⟨hzz, _⟩ := bplus_D_split _ _
          (atomsL_bClose p (bFold p rL) (atomsL_bArg_bFold rL p).2) (atomsL_D _ _)
          (nfSum_bFold_bClose rL p).2 (nfSum_D _ _) (List.cons_ne_nil _ _) qq aa hD
        exact bClose_bFold_ne_zero rL p hc hzz
      · cases hst : (bFold p rL).2 with
        | none =>
          rw [(bot_none p uu rL hpu2 hst).1] at hD
          obtain ⟨hzz, _⟩ := bplus_D_split _ _ (atomsL_bArg_bFold rL p).2 (atomsL_D _ _)
            (nfSum_bFold_bClose rL p).1 (nfSum_D _ _) (List.cons_ne_nil _ _) qq aa hD
          exact hfst hzz
        | some a =>
          rw [(bot_some p uu rL a hpu2 hst).1] at hD
          obtain ⟨hzz, _⟩ := bplus_D_split _ _ (atomsL_bArg_bFold rL p).2 (atomsL_D _ _)
            (nfSum_bFold_bClose rL p).1 (nfSum_D _ _) (List.cons_ne_nil _ _) qq aa hD
          exact hfst hzz
  have hrLn : rL = .nil := by
    by_cases hc : rL = .nil
    · exact hc
    · exfalso
      rw [bot_append p uu rL hpu] at hD
      obtain ⟨hzz, _⟩ := bplus_D_split _ _
        (atomsL_bClose p (bFold p rL) (atomsL_bArg_bFold rL p).2) (atomsL_D _ _)
        (nfSum_bFold_bClose rL p).2 (nfSum_D _ _) (List.cons_ne_nil _ _) qq aa hD
      exact bClose_bFold_ne_zero rL p hc hzz
  subst hrLn
  refine ⟨rfl, ?_, ?_⟩
  · rw [hMt, bot_append p uu .nil hpu,
      show bClose p (bFold p (.nil : B)) = BT.zero from rfl]
    exact bplus_zero_left _ (nfSum_D uu BT.zero)
  · have hqs : nodeAtB 0 (dropLastB t) k = some (wk, uk, rk, dropLastB ck) :=
      nodeAtB_dropLast t 0 k wk uk rk ck hksp (by omega) hq
    rw [bMark_bK (dropLastB t) k wk uk rk (dropLastB ck) hsleaf hqs, tt2,
      if_pos (show ((.nil : B) == (.nil : B)) = true from rfl)]

theorem farMark (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true) (hz : bVal (dropLastB t) ≠ BT.zero)
    (k : Nat) (hk1 : admB t (j0B t) < k) (hk2 : k ≤ j0B t) (hok : markOKB t k = true) :
    (botOf 0 t).2.2 = .nil
      ∧ bMark t k = BT.D (botOf 0 t).2.1 BT.zero
      ∧ bMark (dropLastB t) k = BT.D (botOf 0 t).1 BT.zero :=
  farMark_aux t hnf h1 hprin hz (botOf 0 t).1 (botOf 0 t).2.1 (botOf 0 t).2.2 rfl k hk1 hk2 hok

/-! ### 21. 型 1-6 の枝、`Mark` の側 -/

/-- **`runAux` の型 1-6 の枝** (要求は `Mark m`)。 -/
theorem runAux_main_mark (g : Nat) (t : B) (m : Int) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = true)
    (hzv : bVal (dropLastB t) ≠ BT.zero)
    (hal : AllowedB t (some m))
    (tbl : Trans.Recal.Memo) (hs : SoundB tbl)
    (ih : ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tb).1
            = bVal (dropLastB t)
          ∧ SoundB ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) none).run tb).2)
    (ihm : ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0))
             (some ((admB t (j0B t) : Nat) : Int))).run tb).1
            = bMark (dropLastB t) (admB t (j0B t))
          ∧ SoundB ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0))
             (some ((admB t (j0B t) : Nat) : Int))).run tb).2)
    (ihm2 : m < lenI (psM (matB t 0)) - 1 → ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) (some m)).run tb).1
            = bMark (dropLastB t) m.toNat
          ∧ SoundB ((Trans.Recal.runAux g (psM (matB (dropLastB t) 0)) (some m)).run tb).2) :
    ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) (some m)).run tbl).1 = bValReq t (some m)
      ∧ SoundB ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) (some m)).run tbl).2 := by
  have hne : t ≠ .nil := ne_nil_of_size t h1
  have hleaf : t ≠ .nd 0 .nil .nil := ne_leaf_of_size t h1
  have hsleaf : dropLastB t ≠ .nd 0 .nil .nil := by
    intro hc
    exact hzv (by rw [hc]; exact bVal_leaf)
  obtain ⟨k, hkm, hkok⟩ : ∃ k : Nat, (some m : Option Int) = some ((k : Nat) : Int)
      ∧ markOKB t k = true := by
    rcases hal with h | h
    · exact absurd h (by intro hc; cases hc)
    · exact h
  have hmk : m = ((k : Nat) : Int) := Option.some.inj hkm
  subst hmk
  have hkn : (((k : Nat) : Int)).toNat = k := toNat_cast k
  have hbv : bValReq t (some ((k : Nat) : Int)) = bMark t k := by
    show bMark t (((k : Nat) : Int)).toNat = _
    rw [hkn]
  have hklt : k < sizeB t := lastSpine_lt t k (markOKB_spine t k hkok)
  cases hf : tbl.find? (fun z =>
      z.1 == (psM (matB t 0), (some ((k : Nat) : Int) : Option Int))) with
  | some pp =>
    rw [runHit g _ (some ((k : Nat) : Int)) tbl pp hf]
    obtain ⟨hg, he⟩ := goodB_of_find hs hf
    exact ⟨hg t (some ((k : Nat) : Int)) hnf he (Or.inr ⟨k, rfl, hkok⟩), hs⟩
  | none =>
    obtain ⟨hv0, hsd0⟩ := ih tbl hs
    have ht1 : ((Trans.Recal.runAux g (predP (psM (matB t 0))) none).run tbl).1
        = bVal (dropLastB t) := by
      rw [predP_matB t h1]
      exact hv0
    have hne0 : (bVal (dropLastB t) == BT.zero) = false := bt_beq_false _ _ hzv
    have hc1 : (mainC1 g (psM (matB t 0)) tbl).1 = bMark (dropLastB t) (admB t (j0B t)) := by
      rw [mainC1_tree t h1 hprin]
      exact (ihm _ hsd0).1
    have hsd1 : SoundB (mainC1 g (psM (matB t 0)) tbl).2 := by
      rw [mainC1_tree t h1 hprin]
      exact (ihm _ hsd0).2
    have hlenI : lenI (psM (matB t 0)) - 1 = ((sizeB t - 1 : Nat) : Int) := lenI_sub_one t h1
    have hgpl : (gp1 (psM (matB t 0)) (lenI (psM (matB t 0)) - 1)).toNat = (botOf 0 t).2.1 := by
      rw [hlenI, gp1_last t hne, toNat_cast]
    by_cases hlt : ((k : Nat) : Int) < lenI (psM (matB t 0)) - 1
    · have hklt' : k + 1 < sizeB t := by
        rw [hlenI] at hlt
        omega
      have hoks : markOKB (dropLastB t) k = true :=
        markOKB_dropLast t k h1 hsleaf hkok hklt'
      obtain ⟨hoksj, hoktj⟩ := markOKB_admB_j0 t hnf h1 hprin hzv
      have hc2 : mainC2 (psM (matB t 0)) (mainC1 g (psM (matB t 0)) tbl).1
          = bMark t (admB t (j0B t)) := by
        rw [mainC2_tree t h1 hprin, hc1]
        exact mkC2_glue t hnf h1 hprin hzv
      have hc0 : (mainC0 g (psM (matB t 0)) ((k : Nat) : Int) tbl).1
          = bMark (dropLastB t) k := by
        show ((Trans.Recal.runAux g (predP (psM (matB t 0)))
          (some ((k : Nat) : Int))).run (mainC1 g (psM (matB t 0)) tbl).2).1 = _
        rw [predP_matB t h1]
        have := (ihm2 hlt _ hsd1).1
        rw [hkn] at this
        exact this
      have hsd2 : SoundB (mainC0 g (psM (matB t 0)) ((k : Nat) : Int) tbl).2 := by
        show SoundB ((Trans.Recal.runAux g (predP (psM (matB t 0)))
          (some ((k : Nat) : Int))).run (mainC1 g (psM (matB t 0)) tbl).2).2
        rw [predP_matB t h1]
        exact (ihm2 hlt _ hsd1).2
      have hval : markVal (psM (matB t 0)) (mainC0 g (psM (matB t 0)) ((k : Nat) : Int) tbl).1
          (mainC1 g (psM (matB t 0)) tbl).1 = bMark t k := by
        show (if isMarkedB (mainC0 g (psM (matB t 0)) ((k : Nat) : Int) tbl).1
                  (mainC1 g (psM (matB t 0)) tbl).1 = true then
                (replMark (Trans.Dict.BT.size (mainC0 g (psM (matB t 0)) ((k : Nat) : Int) tbl).1
                    + mainDep (mainC1 g (psM (matB t 0)) tbl).1
                        (mainC2 (psM (matB t 0)) (mainC1 g (psM (matB t 0)) tbl).1))
                  (mainC0 g (psM (matB t 0)) ((k : Nat) : Int) tbl).1
                  (mainC1 g (psM (matB t 0)) tbl).1
                  (mainC2 (psM (matB t 0)) (mainC1 g (psM (matB t 0)) tbl).1)).getD BT.zero
              else BT.D (gp1 (psM (matB t 0)) (lenI (psM (matB t 0)) - 1)).toNat BT.zero) = _
        rw [hc2, hc0, hc1]
        by_cases hkle : k ≤ admB t (j0B t)
        · rw [if_pos (isMarkedB_bMark t k (admB t (j0B t)) hkle hoks hkok hoksj hoktj),
            subst_bMark' t k (admB t (j0B t)) hkle hoks hkok hoksj hoktj _ (by
              show BT.size (bMark (dropLastB t) k)
                  + BT.size (bMark (dropLastB t) (admB t (j0B t)))
                  + BT.size (bMark t (admB t (j0B t))) + 4
                ≤ BT.size (bMark (dropLastB t) k)
                  + (BT.size (bMark (dropLastB t) (admB t (j0B t)))
                    + BT.size (bMark t (admB t (j0B t))) + 4)
              omega)]
          rfl
        · -- `jn1 < k`: 印は右端の道の上に無く、fallback がそのまま答
          have hkj0 : k ≤ j0B t := by
            refine spine_dropLast_le t k ?_
            exact mem_dropLast_of_ne_last _ _ _ (lastSpine_getLast t hne)
              (markOKB_spine t k hkok) (by omega)
          obtain ⟨hrLn, hMtk, hMsk⟩ :=
            farMark t hnf h1 hprin hzv k (by omega) hkj0 hkok
          obtain ⟨w', v, r, c, hq, hMt, hMs, hEq, hLt⟩ := markPair t hnf h1 hprin hzv
          obtain ⟨_, hSj⟩ := hLt (by omega)
          have hc1' : bMark (dropLastB t) (admB t (j0B t))
              = BT.D v (BT.D (botOf 0 t).1 BT.zero) := by
            rw [hMs, hSj, hrLn, if_pos (show ((.nil : B) == (.nil : B)) = true from rfl)]
          rw [hMsk, hc1', if_neg (by
            rw [isMarkedB_D_zero (botOf 0 t).1 v]
            exact Bool.noConfusion), hgpl, hMtk]
      rw [run_main_miss_mark_lt g (psM (matB t 0)) ((k : Nat) : Int) tbl (bVal (dropLastB t))
        (isReducedP_matB t hnf) (lenI_ne_one t h1) hprin ht1 hne0 hlt hf]
      refine ⟨by rw [hval]; exact hbv.symm, ?_⟩
      show SoundB (((psM (matB t 0), (some ((k : Nat) : Int) : Option Int)),
        markVal (psM (matB t 0)) (mainC0 g (psM (matB t 0)) ((k : Nat) : Int) tbl).1
          (mainC1 g (psM (matB t 0)) tbl).1) :: (mainC0 g (psM (matB t 0)) ((k : Nat) : Int) tbl).2)
      rw [hval, ← hbv]
      exact SoundB_cons hsd2 (goodB_mk t (some ((k : Nat) : Int)))
    · have hkeq : k = sizeB t - 1 := by
        rw [hlenI] at hlt
        omega
      have hMtk : bMark t k = BT.D (botOf 0 t).2.1 BT.zero := by
        rw [hkeq, bMark_bK t (sizeB t - 1) (botOf 0 t).1 (botOf 0 t).2.1 (botOf 0 t).2.2 .nil
          hleaf (nodeAtB_last t 0 hne), bK_nil]
      rw [run_main_miss_mark_ge g (psM (matB t 0)) ((k : Nat) : Int) tbl (bVal (dropLastB t))
        (isReducedP_matB t hnf) (lenI_ne_one t h1) hprin ht1 hne0 hlt hf]
      have hans : BT.D (gp1 (psM (matB t 0)) (lenI (psM (matB t 0)) - 1)).toNat BT.zero
          = bValReq t (some ((k : Nat) : Int)) := by
        rw [hgpl, hbv, hMtk]
      refine ⟨hans, ?_⟩
      show SoundB (((psM (matB t 0), (some ((k : Nat) : Int) : Option Int)),
        BT.D (gp1 (psM (matB t 0)) (lenI (psM (matB t 0)) - 1)).toNat BT.zero)
          :: (mainC1 g (psM (matB t 0)) tbl).2)
      rw [hans]
      exact SoundB_cons hsd1 (goodB_mk t (some ((k : Nat) : Int)))

/-! ### 測定 (凍結)

証明した式をそのまま母集団の上で回したもの。負の結果も含む。 -/

-- 1. **`isAdm` = 「潰されない」** (証明ずみ)。標準形の上では全位置で。
#guard (popNFB 3 6).all fun t =>
  (List.range (sizeB t)).all fun i =>
    match nodeAtB 0 t i with
    | some (w', u, r, c) => isAdmB t i == !(collB w' u r c)
    | none => false
-- 1'. **負の結果**: 標準形を外すと `i = 0` で破れる。`i ≥ 1` なら標準形は要らない。
#guard !((((List.range 5).flatMap (enumNodes 3)).filter fun t => t != .nil).all fun t =>
  (List.range (sizeB t)).all fun i =>
    match nodeAtB 0 t i with
    | some (w', u, r, c) => isAdmB t i == !(collB w' u r c)
    | none => false)
#guard (((List.range 5).flatMap (enumNodes 3)).filter fun t => t != .nil).all fun t =>
  (List.range (sizeB t)).all fun i =>
    i == 0 ||
      (match nodeAtB 0 t i with
       | some (w', u, r, c) => isAdmB t i == !(collB w' u r c)
       | none => false)
-- 1''. **負の結果**: `markOKB` は「鎖の上 かつ 許された」と同値ではない (38 か所)。
#guard ((popNFB 3 6).map fun t =>
    ((List.range (sizeB t)).filter fun m =>
      !(markOKB t m == (decide (m ∈ lastSpine t) && isAdmB t m))).length).foldl (· + ·) 0
  == 38
-- そのうち 37 か所は「潰されているのに寄与が 1 つの `D`」の側。逆向き (証明した向き) は正しい。
#guard ((popNFB 3 6).map fun t =>
    ((List.range (sizeB t)).filter fun m =>
      markOKB t m && !(decide (m ∈ lastSpine t) && isAdmB t m)).length).foldl (· + ·) 0
  == 37

-- 2. **側条件** (`markOKB_admB_j0`、証明ずみ)。
#guard (pop6 3 6).all fun t =>
  markOKB (dropLastB t) (admB t (j0B t)) && markOKB t (admB t (j0B t))
#guard (pop6 4 6).all fun t =>
  markOKB (dropLastB t) (admB t (j0B t)) && markOKB t (admB t (j0B t))

-- 3. **糊** (`mkC2_glue`、証明ずみ)。
#guard (pop6 3 6).all fun t =>
  mkC2 (psM (matB t 0)) ((j0B t : Nat) : Int) ((sizeB t - 1 : Nat) : Int)
      (tyMainB t (j0B t) (sizeB t - 1)) (bMark (dropLastB t) (admB t (j0B t)))
    == bMark t (admB t (j0B t))
#guard (pop6 4 6).all fun t =>
  mkC2 (psM (matB t 0)) ((j0B t : Nat) : Int) ((sizeB t - 1 : Nat) : Int)
      (tyMainB t (j0B t) (sizeB t - 1)) (bMark (dropLastB t) (admB t (j0B t)))
    == bMark t (admB t (j0B t))

-- 4. 底のデータ (`botSpine`、証明ずみ): `j0` の節の子は `nd uu rL nil`、位置の関係も。
#guard (pop6 3 6).all fun t =>
  (match nodeAtB 0 t (j0B t) with
   | some (_, p, _, c) => (p == (botOf 0 t).1) && (c == B.nd (botOf 0 t).2.1 (botOf 0 t).2.2 .nil)
   | none => false)
  && (j0B t + 1 + sizeB (botOf 0 t).2.2 == sizeB t - 1)

-- 5. 三つの形 (証明ずみ)。ty 2/4 は 16 個、うち 12 個が `t34` の「そのまま」側。
#guard ((pop6 3 6).filter fun t =>
  let ty := tyMainB t (j0B t) (sizeB t - 1)
  ty == 2 || ty == 4).length == 16
#guard ((pop6 3 6).filter fun t =>
  let b := botOf 0 t
  let ty := tyMainB t (j0B t) (sizeB t - 1)
  (ty == 2 || ty == 4) && ((bFold b.1 b.2.2).2 == none)).length == 12
-- `jn1 ≠ j0` は 30 個 (ty 2:8, ty 4:8, ty 5:8, ty 6:6)。
#guard ((pop6 3 6).filter fun t => decide (admB t (j0B t) < j0B t)).length == 30

-- 6. **(R')** 型 1-6 の枝で要求される印は `s` の側でも意味を持つ (`markOKB_dropLast`)。
#guard (pop6 3 6).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m && decide (m + 1 < sizeB t)) || markOKB (dropLastB t) m
-- 6'. **負の結果**: 型 0 の添字を入れると破れる (`bVal (dropLastB t) = 0` の 2 つ)。
#guard ((popNFB 3 6).filter fun t =>
  !((List.range (sizeB t)).all fun m =>
    !(markOKB t m && decide (m + 1 < sizeB t)) || markOKB (dropLastB t) m)).length == 2

-- 7. **(G9)** `jn1 < m ≤ j0` では、印は `t` で `psi_uu(0)`、`s` で `psi_p(0)` (`farMark`)。
#guard (pop6 3 6).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m && decide (admB t (j0B t) < m) && decide (m ≤ j0B t))
      || (((botOf 0 t).2.2 == .nil)
          && (bMark t m == BT.D (botOf 0 t).2.1 BT.zero)
          && (bMark (dropLastB t) m == BT.D (botOf 0 t).1 BT.zero))

-- 8. 枝そのもの (`runAux_main` / `runAux_main_mark`、証明ずみ): 参照実装と合う。
#guard (pop6 3 6).all fun t => transPort (psM (matB t 0)) == bVal t
#guard (pop6 3 6).all fun t =>
  (List.range (sizeB t)).all fun m =>
    !(markOKB t m) || markRun (psM (matB t 0)) (Int.ofNat m) == bMark t m

/-! ### 公理の確認 -/

end

/-! ## §60 THE OUTER INDUCTION — AND THE PORT CLOSES

    runAux_sum_mark   the one branch nobody had done: type -2 with `req = some m`
    runAux_index      the induction that runs all four branches, on the number of nodes
    transPort_bVal    `Trans (psM (matB t 0)) = bVal t`        — §48, now a THEOREM
    markRun_bMark     `Mark m (psM (matB t 0)) = bMark t m`    — §49, now a THEOREM

§52, §55, §56 and §59 proved the four branches of `runAux` one at a time, each of them taking
the values of its recursive calls as hypotheses.  This section supplies those hypotheses, and
with them the two measurements that the whole port was written to justify become theorems.

THE MISSING ARM.  `runAux`'s `ppair` branch has a `some m` arm that §55 did not do:

    let lastq := ((ppair M).getLast?).getD []
    let j0    := j1 - lastq.length + 1
    if lastq == zeroPS then pure bOne else runAux f lastq (some (m - j0))

**The algorithm never reaches it.**  Run `transPort` on every one of the 670 normal-form indices
of `popNFB 3 6` and scan every memo key: ZERO keys ask for a `Mark` of a non-principal matrix.
The only `Mark` request is the main branch's, and it goes to `Pred`, which keeps `nd 0 nil a`
principal.  But 227 of those indices ARE non-principal and DO have `markOKB` positions, so a
theorem quantified over `AllowedB` has to cover the arm anyway.  Both counts are frozen as
guards at the end.

It is small.  Write `t = nd v r c`, `lastBlk t = nd v nil c` (the last top-level addend) and
`lastBlkOff t = sizeB r` (its root's preorder position):

    sumLast_matB     `lastq` IS `psM (matB (lastBlk t) 0)`   — `ppair_matB`, and the last block
    sumJ0_matB       the algorithm's `j0` IS `lastBlkOff t`
    markIn_lastBlk   the mark transfers to the block verbatim, because a top-level node's
                     contribution does not see its left siblings: the normal form forces its
                     level to 0, and `bK 0 0 r c` is `psi_0(bArg 0 c)` whatever `r` is

with one exception, and it is the `1 +` convention again.  When the last addend is `nd 0 nil nil`
its `bMark` is `zero` by definition, `lastq` is `zeroPS`, and both sides answer `bOne`
(`bMark_blk_zero`).  101 of the 227 take that side.

THE INDUCTION.  `runAux_index` is a strong induction on the number of nodes, with the fuel a
separate parameter bounded below.  The four branches, in `runAux`'s own order:

    sizeB t = 1                runAux_leaf                                        (§52)
    not principal              runAux_sum / runAux_sum_mark, blocks `topSplit t`   (§55, above)
    bVal (dropLastB t) = 0     runAux_type0 / runAux_type0_mark                    (§56)
    otherwise                  runAux_main / runAux_main_mark                      (§59)

The recursive arguments shrink: `dropLastB t` by `sizeB_dropLast`, the blocks by
`sizeB_topSplit_lt`.  That last one needs a fact no branch states — a non-principal index has a
left sibling at the top, because `prin_of_deep` makes `nd v nil c` principal outright — and
without it the one-block case would recurse into itself.  `markOKB_admB_j0` (§59) and
`markOKB_dropLast` supply the `AllowedB` of the two `some` recursive calls of the main branch,
`markOKB_lastBlk_gen` the one of the sum branch.

Fuel is not a fight: `transFuel M = 40 + 6 * (M.length + maxE M)` and `M.length = sizeB t` by
`sizeB_matB`, so `sizeB t ≤ transFuel (psM (matB t 0))` outright.

WHAT IS NOW A THEOREM.  §48's `bVal` and §49's `bMark` were measurements.  `transPort_bVal` and
`markRun_bMark` make them theorems — for EVERY normal-form index and EVERY `markOKB` position,
not for an enumeration.  Nothing about `Trans` or `Mark` is measured any more.  What is still
measured here is only the negative fact above, that the arm is unreachable in practice, and the
two counts; both are statements about the enumeration, not about the algorithm. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### 1. 最後の最上位の加数 -/

/-- 最後の最上位の加数。 -/
def lastBlk : B → B
  | .nil => .nil
  | .nd v _ c => .nd v .nil c

/-- その根の前順位置。 -/
def lastBlkOff : B → Nat
  | .nil => 0
  | .nd _ r _ => sizeB r

theorem sizeB_lastBlk : ∀ (t : B), t ≠ .nil → lastBlkOff t + sizeB (lastBlk t) = sizeB t
  | .nil, h => absurd rfl h
  | .nd v r c, _ => by
      show sizeB r + (sizeB (.nil : B) + 1 + sizeB c) = sizeB r + 1 + sizeB c
      show sizeB r + (0 + 1 + sizeB c) = sizeB r + 1 + sizeB c
      omega

theorem getLast?_snoc {α : Type _} : ∀ (l : List α) (a : α), (l ++ [a]).getLast? = some a
  | [], a => rfl
  | x :: rest, a => by
      show ((x :: (rest ++ [a])) : List α).getLast? = some a
      rw [getLast?_cons_of_ne_nil x (rest ++ [a]) (by
        intro hc
        exact absurd (List.append_eq_nil_iff.mp hc).2 (by intro hcc; cases hcc))]
      exact getLast?_snoc rest a

/-- **(U)** アルゴリズムが見る最後のブロックは、最後の最上位の加数。 -/
theorem sumLast_matB : ∀ (t : B), t ≠ .nil →
    (((ppair (psM (matB t 0))).getLast?).getD []) = psM (matB (lastBlk t) 0)
  | .nil, h => absurd rfl h
  | .nd v r c, _ => by
      rw [ppair_matB]
      show ((((topSplit r ++ [B.nd v .nil c]).map
        (fun s => psM (matB s 0))).getLast?).getD []) = psM (matB (B.nd v .nil c) 0)
      rw [List.map_append]
      show ((((topSplit r).map (fun s => psM (matB s 0))
        ++ [psM (matB (B.nd v .nil c) 0)]).getLast?).getD []) = _
      rw [getLast?_snoc]
      rfl

/-- **(T)** アルゴリズムの `j0` は最後のブロックの根の前順位置。 -/
theorem sumJ0_matB (t : B) (h : t ≠ .nil) :
    lenI (psM (matB t 0)) - 1 - (((psM (matB (lastBlk t) 0)).length : Nat) : Int) + 1
      = ((lastBlkOff t : Nat) : Int) := by
  rw [lenI_matB, psM_len, sizeB_matB]
  have := sizeB_lastBlk t h
  omega

/-- 左の兄弟が無ければ principal。 -/
theorem prin_of_no_sibs (v : Nat) (c : B) (h1 : 1 < sizeB (.nd v .nil c : B)) :
    isPrincipalP (psM (matB (.nd v .nil c) 0)) = true := by
  refine prin_of_deep (matB (.nd v .nil c) 0) ?_ (matB_node_deep v c 0)
  rw [sizeB_matB]
  exact h1

/-- **非 principal なら最後のブロックは真に小さい。** 外側の帰納法が要る測度。 -/
theorem lastBlk_lt (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = false) : sizeB (lastBlk t) < sizeB t := by
  cases t with
  | nil =>
    have h0 : sizeB (.nil : B) = 0 := rfl
    omega
  | nd v r c =>
    have hrne : r ≠ .nil := by
      intro hc
      subst hc
      rw [prin_of_no_sibs v c h1] at hprin
      exact Bool.noConfusion hprin
    have hrp : 0 < sizeB r := sizeB_pos r hrne
    show sizeB (.nil : B) + 1 + sizeB c < sizeB r + 1 + sizeB c
    show 0 + 1 + sizeB c < sizeB r + 1 + sizeB c
    omega

/-! ### 2. 印はブロックへ移る -/

/-- 根の寄与は左の兄弟に依らない (最上位なので `w = u = 0`)。 -/
theorem markIn_lastBlk (r c : B) (k : Nat) (h : sizeB r ≤ k) :
    markIn 0 (.nd 0 r c) k = markIn 0 (.nd 0 (.nil : B) c) (k - sizeB r) := by
  rcases Nat.lt_or_ge k (sizeB r + 1) with hk | hk
  · have hk0 : k = sizeB r := by omega
    subst hk0
    rw [markIn_node,
      show sizeB r - sizeB r = sizeB (.nil : B) from by
        show sizeB r - sizeB r = 0
        omega,
      markIn_node, bK_le 0 0 r c (Nat.le_refl 0), bK_le 0 0 .nil c (Nat.le_refl 0)]
  · obtain ⟨i, rfl⟩ : ∃ i, k = sizeB r + 1 + i := ⟨k - sizeB r - 1, by omega⟩
    rw [markIn_deep,
      show sizeB r + 1 + i - sizeB r = sizeB (.nil : B) + 1 + i from by
        show sizeB r + 1 + i - sizeB r = 0 + 1 + i
        omega,
      markIn_deep]

/-- **(R')** 最後のブロックが `(0,0)` でなければ、印はブロックの印。 -/
theorem bMark_lastBlk (r c : B)
    (hne : (.nd 0 r c : B) ≠ .nd 0 .nil .nil)
    (hbl : (.nd 0 (.nil : B) c : B) ≠ .nd 0 .nil .nil) (k : Nat) (hk : sizeB r ≤ k) :
    bMark (.nd 0 r c) k = bMark (.nd 0 (.nil : B) c) (k - sizeB r) := by
  rw [bMark_eq_markG _ _ hne, bMark_eq_markG _ _ hbl]
  show (markIn 0 (B.nd 0 r c) k).getD .zero
    = (markIn 0 (B.nd 0 (.nil : B) c) (k - sizeB r)).getD .zero
  rw [markIn_lastBlk r c k hk]

/-- 祖先鎖もそのまま移る。 -/
theorem lastSpine_lastBlk (r c : B) (k : Nat) (h : k ∈ lastSpine (.nd 0 r c)) :
    k - sizeB r ∈ lastSpine (.nd 0 (.nil : B) c) := by
  rcases lastSpine_nd_cases 0 r c k h with he | ⟨j, hj, hje⟩
  · rw [show k - sizeB r = 0 from by omega, lastSpine_nd]
    exact List.mem_cons.mpr (Or.inl rfl)
  · rw [show k - sizeB r = 0 + 1 + j from by omega, lastSpine_nd]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hj, rfl⟩)

/-- **(S')** 印が意味を持つ位置もそのまま移る。 -/
theorem markOKB_lastBlk (r c : B)
    (hne : (.nd 0 r c : B) ≠ .nd 0 .nil .nil)
    (hbl : (.nd 0 (.nil : B) c : B) ≠ .nd 0 .nil .nil) (k : Nat)
    (h : markOKB (.nd 0 r c) k = true) :
    markOKB (.nd 0 (.nil : B) c) (k - sizeB r) = true := by
  have hsp : k ∈ lastSpine (.nd 0 r c) := markOKB_spine _ _ h
  have hk : sizeB r ≤ k := lastSpine_ge (.nd 0 r c) k hsp
  have hD : ∃ p a, bMark (.nd 0 r c) k = BT.D p a := by
    have h2 : (match bMark (.nd 0 r c) k with | .D _ _ => true | _ => false) = true :=
      ((Bool.and_eq_true _ _).mp h).2
    cases hb : bMark (.nd 0 r c) k with
    | zero => rw [hb] at h2; exact absurd h2 (by intro hc; exact Bool.noConfusion hc)
    | D p a => exact ⟨p, a, rfl⟩
    | sum x y => rw [hb] at h2; exact absurd h2 (by intro hc; exact Bool.noConfusion hc)
  obtain ⟨p, a, hpa⟩ := hD
  refine markOKB_mk _ _ (lastSpine_lastBlk r c k hsp) p a ?_
  rw [← bMark_lastBlk r c hne hbl k hk]
  exact hpa

/-- **(V)** 最後のブロックが `(0,0)` のときは、印は `1`。 -/
theorem bMark_blk_zero (r : B) (k : Nat)
    (hne : (.nd 0 r (.nil : B) : B) ≠ .nd 0 .nil .nil)
    (h : markOKB (.nd 0 r (.nil : B)) k = true) : bMark (.nd 0 r .nil) k = bOne := by
  have hsp : k ∈ lastSpine (.nd 0 r (.nil : B)) := markOKB_spine _ _ h
  have hk : k = sizeB r := by
    rcases lastSpine_nd_cases 0 r .nil k hsp with he | ⟨j, hj, _⟩
    · exact he
    · exact absurd hj (by intro hc; exact absurd hc (by intro hcc; cases hcc))
  subst hk
  rw [bMark_eq_markG _ _ hne]
  show (markIn 0 (B.nd 0 r (.nil : B)) (sizeB r)).getD .zero = bOne
  rw [markIn_node, bK_le 0 0 r .nil (Nat.le_refl 0)]
  rfl

/-! ### 3. 型 -2 の `Mark` の枝を開く -/

/-- memo に外れた型 -2 の `Mark` の枝、最後のブロックが `(0,0)` のとき。 -/
theorem run_summark_miss_zero (f : Nat) (M : Trans.Recal.PS) (m : Int)
    (tbl : Trans.Recal.Memo)
    (hred : isReducedP M = true) (hj1 : (lenI M - 1 == 0) = false)
    (hprin : isPrincipalP M = false)
    (hz : ((((ppair M).getLast?).getD []) == zeroPS) = true)
    (h : tbl.find? (fun q => q.1 == (M, (some m : Option Int))) = none) :
    (Trans.Recal.runAux (f + 1) M (some m)).run tbl
      = (bOne, ((M, (some m : Option Int)), bOne) :: tbl) := by
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, pure,
    get, getThe, MonadStateOf.get, h, hred, hj1, hprin, hz,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true]
  rfl

/-- memo に外れた型 -2 の `Mark` の枝、ブロックへ潜るとき。 -/
theorem run_summark_miss_rec (f : Nat) (M : Trans.Recal.PS) (m : Int)
    (tbl : Trans.Recal.Memo)
    (hred : isReducedP M = true) (hj1 : (lenI M - 1 == 0) = false)
    (hprin : isPrincipalP M = false)
    (hz : ((((ppair M).getLast?).getD []) == zeroPS) = false)
    (h : tbl.find? (fun q => q.1 == (M, (some m : Option Int))) = none) :
    (Trans.Recal.runAux (f + 1) M (some m)).run tbl
      = (((Trans.Recal.runAux f (((ppair M).getLast?).getD [])
            (some (m - (lenI M - 1 - (((((ppair M).getLast?).getD []).length : Nat) : Int)
              + 1)))).run tbl).1,
         ((M, (some m : Option Int)),
            ((Trans.Recal.runAux f (((ppair M).getLast?).getD [])
              (some (m - (lenI M - 1 - (((((ppair M).getLast?).getD []).length : Nat) : Int)
                + 1)))).run tbl).1)
           :: ((Trans.Recal.runAux f (((ppair M).getLast?).getD [])
                (some (m - (lenI M - 1 - (((((ppair M).getLast?).getD []).length : Nat) : Int)
                  + 1)))).run tbl).2) := by
  rw [Trans.Recal.runAux]
  simp only [StateT.run, bind, StateT.bind, StateT.get, pure,
    get, getThe, MonadStateOf.get, h, hred, hj1, hprin, hz,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true]
  rfl

/-! ### 4. 型 -2 の枝、`Mark` の側 -/

/-- **`runAux` の型 -2 の枝** (要求は `Mark m`)。 -/
theorem runAux_sum_mark (g : Nat) (t : B) (m : Int) (hnf : nfB t = true) (hne : t ≠ .nil)
    (hj1 : (lenI (psM (matB t 0)) - 1 == 0) = false)
    (hprin : isPrincipalP (psM (matB t 0)) = false)
    (hal : AllowedB t (some m))
    (tbl : Trans.Recal.Memo) (hs : SoundB tbl)
    (ih : lastBlk t ≠ .nd 0 .nil .nil → ∀ tb : Trans.Recal.Memo, SoundB tb →
        ((Trans.Recal.runAux g (psM (matB (lastBlk t) 0))
            (some (m - ((lastBlkOff t : Nat) : Int)))).run tb).1
          = bValReq (lastBlk t) (some (m - ((lastBlkOff t : Nat) : Int)))
        ∧ SoundB ((Trans.Recal.runAux g (psM (matB (lastBlk t) 0))
            (some (m - ((lastBlkOff t : Nat) : Int)))).run tb).2) :
    ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) (some m)).run tbl).1 = bValReq t (some m)
      ∧ SoundB ((Trans.Recal.runAux (g + 1) (psM (matB t 0)) (some m)).run tbl).2 := by
  have hsz : 1 < sizeB t := by
    have h0 : 0 < sizeB t := sizeB_pos t hne
    rcases Nat.lt_or_ge 1 (sizeB t) with hlt | hge
    · exact hlt
    · exfalso
      have he : sizeB t = 1 := by omega
      have hz0 : lenI (psM (matB t 0)) - 1 = 0 := by rw [lenI_matB, he]; rfl
      rw [hz0] at hj1
      exact absurd hj1 (by decide)
  obtain ⟨v, r, c, rfl⟩ : ∃ v r c, t = .nd v r c := by
    cases t with
    | nil => exact absurd rfl hne
    | nd v r c => exact ⟨v, r, c, rfl⟩
  have hv0 : v = 0 := by
    have := ((nfLe_nd_iff 0 v r c).mp hnf).1
    omega
  subst hv0
  obtain ⟨k, hkm, hkok⟩ : ∃ k : Nat, (some m : Option Int) = some ((k : Nat) : Int)
      ∧ markOKB (.nd 0 r c) k = true := by
    rcases hal with h | h
    · exact absurd h (by intro hcc; cases hcc)
    · exact h
  have hmk : m = ((k : Nat) : Int) := Option.some.inj hkm
  subst hmk
  have hbv : bValReq (.nd 0 r c) (some ((k : Nat) : Int)) = bMark (.nd 0 r c) k := by
    show bMark (.nd 0 r c) (((k : Nat) : Int)).toNat = _
    rw [toNat_cast]
  have hleaf : (B.nd 0 r c : B) ≠ .nd 0 .nil .nil := ne_leaf_of_size _ hsz
  cases hf : tbl.find? (fun z => z.1 == (psM (matB (B.nd 0 r c) 0),
      (some ((k : Nat) : Int) : Option Int))) with
  | some p =>
    rw [runHit g _ (some ((k : Nat) : Int)) tbl p hf]
    obtain ⟨hg, he⟩ := goodB_of_find hs hf
    exact ⟨hg _ (some ((k : Nat) : Int)) hnf he (Or.inr ⟨k, rfl, hkok⟩), hs⟩
  | none =>
    by_cases hcn : c = (.nil : B)
    · subst hcn
      have hzq : (((ppair (psM (matB (B.nd 0 r (.nil : B)) 0))).getLast?).getD []
          == zeroPS) = true := by
        rw [sumLast_matB _ hne]
        rfl
      have hval : bMark (B.nd 0 r (.nil : B)) k = bOne := bMark_blk_zero r k hleaf hkok
      rw [run_summark_miss_zero g _ _ tbl (isReducedP_matB _ hnf) hj1 hprin hzq hf,
        ← hval, ← hbv]
      exact ⟨rfl, SoundB_cons hs (goodB_mk (B.nd 0 r (.nil : B)) (some ((k : Nat) : Int)))⟩
    · have hbl : lastBlk (B.nd 0 r c) ≠ .nd 0 .nil .nil := by
        show (B.nd 0 (.nil : B) c : B) ≠ .nd 0 .nil .nil
        intro hcc
        apply hcn
        injection hcc with _ _ h3
      have hzq : (((ppair (psM (matB (B.nd 0 r c) 0))).getLast?).getD []
          == zeroPS) = false := by
        rw [sumLast_matB _ hne]
        show (psM (matB (B.nd 0 (.nil : B) c) 0) == zeroPS) = false
        rw [psM_matB_eq_zeroPS 0 c, beqB_false c .nil hcn]
        rfl
      have hkge : sizeB r ≤ k := lastSpine_ge _ k (markOKB_spine _ _ hkok)
      have hnum : ((((k : Nat) : Int)
          - ((lastBlkOff (B.nd 0 r c) : Nat) : Int))).toNat = k - sizeB r := by
        show ((((k : Nat) : Int) - ((sizeB r : Nat) : Int))).toNat = k - sizeB r
        omega
      have hbvb : bValReq (lastBlk (B.nd 0 r c))
            (some (((k : Nat) : Int) - ((lastBlkOff (B.nd 0 r c) : Nat) : Int)))
          = bMark (B.nd 0 r c) k := by
        show bMark (lastBlk (B.nd 0 r c)) ((((k : Nat) : Int)
          - ((lastBlkOff (B.nd 0 r c) : Nat) : Int)).toNat) = _
        rw [hnum]
        exact (bMark_lastBlk r c hleaf hbl k hkge).symm
      obtain ⟨hv1, hsd1⟩ := ih hbl tbl hs
      rw [run_summark_miss_rec g _ _ tbl (isReducedP_matB _ hnf) hj1 hprin hzq hf,
        sumLast_matB _ hne, sumJ0_matB _ hne, hv1, hbvb, ← hbv]
      exact ⟨rfl, SoundB_cons hsd1 (goodB_mk (B.nd 0 r c) (some ((k : Nat) : Int)))⟩

/-! ### 5. 外側の帰納法が使う測度と標準形 -/

theorem sizeB_topSplit_le : ∀ (x : B), ∀ s ∈ topSplit x, sizeB s ≤ sizeB x
  | .nil, s, hs => by
      have h' : s ∈ ([] : List B) := hs
      cases h'
  | .nd v r a, s, hs => by
      rcases List.mem_append.mp hs with h | h
      · have := sizeB_topSplit_le r s h
        show sizeB s ≤ sizeB r + 1 + sizeB a
        omega
      · rw [List.mem_singleton.mp h]
        show sizeB (.nil : B) + 1 + sizeB a ≤ sizeB r + 1 + sizeB a
        show 0 + 1 + sizeB a ≤ sizeB r + 1 + sizeB a
        omega

/-- **非 principal なら、どのブロックも節が減る。** -/
theorem sizeB_topSplit_lt (t : B) (h1 : 1 < sizeB t)
    (hprin : isPrincipalP (psM (matB t 0)) = false) :
    ∀ s ∈ topSplit t, sizeB s < sizeB t := by
  cases t with
  | nil =>
    have h0 : sizeB (.nil : B) = 0 := rfl
    omega
  | nd v r c =>
    intro s hsm
    have hrne : r ≠ .nil := by
      intro hc
      subst hc
      rw [prin_of_no_sibs v c h1] at hprin
      exact Bool.noConfusion hprin
    have hrp : 0 < sizeB r := sizeB_pos r hrne
    rcases List.mem_append.mp hsm with h | h
    · have := sizeB_topSplit_le r s h
      show sizeB s < sizeB r + 1 + sizeB c
      omega
    · rw [List.mem_singleton.mp h]
      show sizeB (.nil : B) + 1 + sizeB c < sizeB r + 1 + sizeB c
      show 0 + 1 + sizeB c < sizeB r + 1 + sizeB c
      omega

theorem nfB_topSplit : ∀ (x : B), nfB x = true → ∀ s ∈ topSplit x, nfB s = true
  | .nil, _, s, hs => by
      have h' : s ∈ ([] : List B) := hs
      cases h'
  | .nd v r a, hnf, s, hs => by
      obtain ⟨hv, hr, ha⟩ := (nfLe_nd_iff 0 v r a).mp hnf
      rcases List.mem_append.mp hs with h | h
      · exact nfB_topSplit r hr s h
      · rw [List.mem_singleton.mp h]
        exact (nfLe_nd_iff 0 v .nil a).mpr ⟨hv, rfl, ha⟩

theorem lastBlk_mem : ∀ (t : B), t ≠ .nil → lastBlk t ∈ topSplit t
  | .nil, h => absurd rfl h
  | .nd _ _ _, _ => List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

theorem lastBlk_ne_nil : ∀ (t : B), t ≠ .nil → lastBlk t ≠ .nil
  | .nil, h => absurd rfl h
  | .nd _ _ _, _ => by intro hc; exact B.noConfusion hc

theorem lastBlkOff_le : ∀ (t : B) (k : Nat), k ∈ lastSpine t → lastBlkOff t ≤ k
  | .nil, k, h => by
      have h' : k ∈ ([] : List Nat) := h
      cases h'
  | .nd v r c, k, h => lastSpine_ge (.nd v r c) k h

/-- **(S')**、標準形の添字について。 -/
theorem markOKB_lastBlk_gen (t : B) (hnf : nfB t = true) (h1 : 1 < sizeB t)
    (hbl : lastBlk t ≠ .nd 0 .nil .nil) (k : Nat) (h : markOKB t k = true) :
    markOKB (lastBlk t) (k - lastBlkOff t) = true := by
  cases t with
  | nil =>
    have h0 : sizeB (.nil : B) = 0 := rfl
    omega
  | nd v r c =>
    have hv0 : v = 0 := by
      have := ((nfLe_nd_iff 0 v r c).mp hnf).1
      omega
    subst hv0
    exact markOKB_lastBlk r c (ne_leaf_of_size _ h1) hbl k h

/-! ### 6. 外側の帰納法 -/

/-- **移植の要。** 節の個数についての強帰納法で、`runAux` の 4 つの枝を回す。 -/
theorem runAux_index : ∀ (n : Nat) (t : B) (req : Option Int),
    sizeB t ≤ n → nfB t = true → t ≠ .nil → AllowedB t req →
    ∀ (g : Nat), n ≤ g → ∀ (tbl : Trans.Recal.Memo), SoundB tbl →
      ((Trans.Recal.runAux g (psM (matB t 0)) req).run tbl).1 = bValReq t req
        ∧ SoundB ((Trans.Recal.runAux g (psM (matB t 0)) req).run tbl).2 := by
  intro n
  induction n with
  | zero =>
    intro t req hsz _ hne _ _ _ _ _
    exact absurd hsz (by
      have := sizeB_pos t hne
      omega)
  | succ n' ihn =>
    intro t req hsz hnf hne hal g hg tbl hs
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hg' : n' ≤ g' := by omega
    rcases Nat.lt_or_ge 1 (sizeB t) with h1 | hle1
    · have hj1 : (lenI (psM (matB t 0)) - 1 == 0) = false := by
        rw [lenI_matB]
        refine decide_eq_false ?_
        omega
      by_cases hprin : isPrincipalP (psM (matB t 0)) = true
      · have hd : sizeB (dropLastB t) ≤ n' := by
          have := sizeB_dropLast t hne
          omega
        have hdnf : nfB (dropLastB t) = true := nfLe_dropLast t 0 hnf
        have hdne : dropLastB t ≠ .nil := by
          intro hc
          have hh := sizeB_dropLast t hne
          rw [hc] at hh
          have h0 : sizeB (.nil : B) = 0 := rfl
          omega
        have ihd : ∀ tb : Trans.Recal.Memo, SoundB tb →
            ((Trans.Recal.runAux g' (psM (matB (dropLastB t) 0)) none).run tb).1
                = bVal (dropLastB t)
              ∧ SoundB ((Trans.Recal.runAux g' (psM (matB (dropLastB t) 0)) none).run tb).2 :=
          fun tb htb => ihn (dropLastB t) none hd hdnf hdne (Or.inl rfl) g' hg' tb htb
        by_cases hzv : bVal (dropLastB t) = BT.zero
        · cases req with
          | none => exact runAux_type0 g' t hnf h1 hprin hzv tbl hs ihd
          | some mm => exact runAux_type0_mark g' t mm hnf h1 hprin hzv hal tbl hs ihd
        · have hokj := markOKB_admB_j0 t hnf h1 hprin hzv
          have ihm : ∀ tb : Trans.Recal.Memo, SoundB tb →
              ((Trans.Recal.runAux g' (psM (matB (dropLastB t) 0))
                   (some ((admB t (j0B t) : Nat) : Int))).run tb).1
                  = bMark (dropLastB t) (admB t (j0B t))
                ∧ SoundB ((Trans.Recal.runAux g' (psM (matB (dropLastB t) 0))
                   (some ((admB t (j0B t) : Nat) : Int))).run tb).2 :=
            fun tb htb => ihn (dropLastB t) (some ((admB t (j0B t) : Nat) : Int)) hd hdnf hdne
              (Or.inr ⟨admB t (j0B t), rfl, hokj.1⟩) g' hg' tb htb
          cases req with
          | none => exact runAux_main g' t hnf h1 hprin hzv tbl hs ihd ihm
          | some mm =>
            have ihm2 : mm < lenI (psM (matB t 0)) - 1 → ∀ tb : Trans.Recal.Memo, SoundB tb →
                ((Trans.Recal.runAux g' (psM (matB (dropLastB t) 0)) (some mm)).run tb).1
                    = bMark (dropLastB t) mm.toNat
                  ∧ SoundB ((Trans.Recal.runAux g' (psM (matB (dropLastB t) 0))
                      (some mm)).run tb).2 := by
              intro hlt tb htb
              obtain ⟨k, hkm, hkok⟩ : ∃ k : Nat, (some mm : Option Int) = some ((k : Nat) : Int)
                  ∧ markOKB t k = true := by
                rcases hal with h | h
                · exact absurd h (by intro hc; cases hc)
                · exact h
              have hmk : mm = ((k : Nat) : Int) := Option.some.inj hkm
              subst hmk
              have hsleaf : dropLastB t ≠ .nd 0 .nil .nil := by
                intro hc
                exact hzv (by rw [hc]; exact bVal_leaf)
              have hklt : k + 1 < sizeB t := by
                rw [lenI_matB] at hlt
                omega
              exact ihn (dropLastB t) (some ((k : Nat) : Int)) hd hdnf hdne
                (Or.inr ⟨k, rfl, markOKB_dropLast t k h1 hsleaf hkok hklt⟩) g' hg' tb htb
            exact runAux_main_mark g' t mm hnf h1 hprin hzv hal tbl hs ihd ihm ihm2
      · have hprinf : isPrincipalP (psM (matB t 0)) = false := Bool.eq_false_iff.mpr hprin
        cases req with
        | none =>
          refine runAux_sum g' t hnf hne hj1 hprinf tbl hs ?_
          intro s hsm tb htb
          refine ihn s none ?_ (nfB_topSplit t hnf s hsm) ?_ (Or.inl rfl) g' hg' tb htb
          · have := sizeB_topSplit_lt t h1 hprinf s hsm
            omega
          · obtain ⟨w, cc, hw⟩ := topSplit_shape t s hsm
            rw [hw]
            intro hc
            exact B.noConfusion hc
        | some mm =>
          refine runAux_sum_mark g' t mm hnf hne hj1 hprinf hal tbl hs ?_
          intro hbl tb htb
          obtain ⟨k, hkm, hkok⟩ : ∃ k : Nat, (some mm : Option Int) = some ((k : Nat) : Int)
              ∧ markOKB t k = true := by
            rcases hal with h | h
            · exact absurd h (by intro hc; cases hc)
            · exact h
          have hmk : mm = ((k : Nat) : Int) := Option.some.inj hkm
          subst hmk
          have hkge : lastBlkOff t ≤ k := lastBlkOff_le t k (markOKB_spine t k hkok)
          rw [show ((k : Nat) : Int) - ((lastBlkOff t : Nat) : Int)
              = (((k - lastBlkOff t : Nat)) : Int) from by omega]
          refine ihn (lastBlk t) (some (((k - lastBlkOff t : Nat)) : Int)) ?_
            (nfB_topSplit t hnf (lastBlk t) (lastBlk_mem t hne)) (lastBlk_ne_nil t hne)
            (Or.inr ⟨k - lastBlkOff t, rfl, markOKB_lastBlk_gen t hnf h1 hbl k hkok⟩)
            g' hg' tb htb
          have := lastBlk_lt t h1 hprinf
          omega
    · have hs1 : sizeB t = 1 := by
        have := sizeB_pos t hne
        omega
      obtain ⟨v, rfl⟩ := sizeB_eq_one t hs1
      have hv0 : v = 0 := by
        have := ((nfLe_nd_iff 0 v .nil .nil).mp hnf).1
        omega
      subst hv0
      exact runAux_leaf g' req tbl hs hal

/-! ### 7. §48 と §49 は定理になる -/

theorem sizeB_le_transFuel (t : B) : sizeB t ≤ transFuel (psM (matB t 0)) := by
  show sizeB t ≤ 40 + 6 * ((psM (matB t 0)).length + maxE (psM (matB t 0)))
  rw [psM_len, sizeB_matB]
  omega

/-- **§48 の閉じた形は `Trans` そのもの。** -/
theorem transPort_bVal (t : B) (hnf : nfB t = true) (hne : t ≠ .nil) :
    transPort (psM (matB t 0)) = bVal t := by
  have h := runAux_index (sizeB t) t none (Nat.le_refl _) hnf hne (Or.inl rfl)
    (transFuel (psM (matB t 0))) (sizeB_le_transFuel t) [] SoundB_nil
  show ((Trans.Recal.runAux (transFuel (psM (matB t 0))) (psM (matB t 0)) none).run []).1
    = bVal t
  exact h.1

/-- **§49 の閉じた形は `Mark m` そのもの。** -/
theorem markRun_bMark (t : B) (m : Nat) (hnf : nfB t = true) (h : markOKB t m = true) :
    markRun (psM (matB t 0)) ((m : Nat) : Int) = bMark t m := by
  have hne : t ≠ .nil := by
    intro hc
    have hsp : m ∈ lastSpine t := markOKB_spine t m h
    rw [hc] at hsp
    have h' : m ∈ ([] : List Nat) := hsp
    cases h'
  have hh := runAux_index (sizeB t) t (some ((m : Nat) : Int)) (Nat.le_refl _) hnf hne
    (Or.inr ⟨m, rfl, h⟩) (transFuel (psM (matB t 0))) (sizeB_le_transFuel t) [] SoundB_nil
  show ((Trans.Recal.runAux (transFuel (psM (matB t 0))) (psM (matB t 0))
      (some ((m : Nat) : Int))).run []).1 = bMark t m
  exact hh.1

/-! ### 測定 -/

-- **負の測定: 型 -2 の `Mark` の枝には、走らせても来ない。**
-- memo に積まれる鍵のうち、principal でない行列に `Mark` を要求するものは 1 つも無い。
#guard (popNFB 3 6).all fun t =>
  (memoKeys (psM (matB t 0))).all fun p =>
    match p.1.2 with
    | none => true
    | some _ => isPrincipalP p.1.1
-- それでも `AllowedB` で量化した定理は覆わねばならない。非 principal な標準形の添字は
-- 228 個、そのうち `markOKB` な位置を持つものが 227 個。
#guard ((popNFB 3 6).filter fun t => !(isPrincipalP (psM (matB t 0)))).length == 228
#guard ((popNFB 3 6).filter fun t =>
    !(isPrincipalP (psM (matB t 0)))
      && (List.range (sizeB t)).any (fun m => markOKB t m)).length == 227
-- そのうち 101 個は最後の加数が `(0,0)` で、`bOne` の側に落ちる。
#guard ((popNFB 3 6).filter fun t =>
    !(isPrincipalP (psM (matB t 0))) && (lastBlk t == .nd 0 .nil .nil)
      && (List.range (sizeB t)).any (fun m => markOKB t m)).length == 101
-- (U)(T) の読み替えは非 principal に限らず成り立つ (証明も `t ≠ nil` だけ)。
#guard (popNFB 3 6).all fun t =>
  ((ppair (psM (matB t 0))).getLast?).getD [] == psM (matB (lastBlk t) 0)
#guard (popNFB 3 6).all fun t =>
  let M := psM (matB t 0)
  let lastq := ((ppair M).getLast?).getD []
  (lenI M - 1 - (lastq.length : Int) + 1) == ((lastBlkOff t : Nat) : Int)
#guard (popNFB 4 6).all fun t =>
  let M := psM (matB t 0)
  let lastq := ((ppair M).getLast?).getD []
  (lenI M - 1 - (lastq.length : Int) + 1) == ((lastBlkOff t : Nat) : Int)
-- 燃料は十分。
#guard (popNFB 3 6).all fun t => sizeB t ≤ transFuel (psM (matB t 0))

end

/-! ## §61 BMS STANDARDNESS ON THE INDEX SIDE, AND THE FIRST TWO SUPPLIES

§60 closed the port: `transPort (psM (matB t 0)) = bVal t`.  §61 measures what the region
must be, and hands `certIn_region` the two supplies that do not need the limit clause.

THE PROBLEM §60 LEFT.  The generalised region is `nfB` — the Trans-side reduced form — and
on it `Hlim`'s clause `lt (value (fsB t n)) (value t)` is FALSE.  The three smallest
failures are `(0,0)(1,0)(2,1)(1,1)`, `(0,0)(1,0)(2,0)(3,1)(2,1)` and
`(0,0)(1,1)(2,1)(3,2)(2,2)`, and all three are NON-STANDARD as Bashicu matrices: no
expansion path from `(0,0)` reaches them.  `nfB` is strictly weaker than BMS standardness.

WHAT THIS SECTION FINDS.  A decidable structural predicate `stdB : B → Bool` that agrees
with the C reference implementation `~/proofs/yaBMS/c/bms -s` on **236 422 matrices**,
with zero mismatches in either direction:

    popNFB 3 6      670   (verdicts frozen verbatim below, as a 670-character string)
    enumB   3 6  16 332   1105 standard
    enumB   4 5   5 101    250 standard
    enumB   3 7 153 421   5507 standard
    enumB   4 6  60 898   1263 standard

and, on a population of a completely different shape — the depth-three expansion closure of
the table's 52 width-two rows, `popB`, 877 matrices reaching **47 columns**, every one of
which the reference calls standard — `stdB` accepts all 877.  So the agreement is not an
artefact of small enumerations.

`stdB` is `nfB` (a node's level is at most its parent's plus one) conjoined with two
conditions, and both are the classical normal-form conditions for a Buchholz-style ψ:

  CNF   the summands of every argument — and of the whole term — descend, `nonIncr`;
  BNF   for a node of level `v` with argument `a`: scanning `a` and descending only
        through nodes of level `≥ v`, every node of level EXACTLY `v` has an argument
        strictly below `a`.  That is `visOK`, and the comparison is `cmpS`, the ordinary
        lexicographic-from-the-left order on descending sums.

THE ONE SURPRISE, worth recording because the first attempt failed on it: Buchholz's own
condition constrains `ψ_u(b)` for EVERY `u ≥ v`, not only `u = v`.  That version is sound
(no false positives) but rejects 75 of the 670 — every index containing the diagonal
`(0,0)(1,1)(2,2)`, which IS standard.  Constraining only `u = v` is exact.  So the pair
sequence system's standard form is NOT Buchholz's normal form; it is the weaker one.

WHAT `stdB` BUYS, measured:

  (i)   `stdB t → stdB (fsB t n)` — closure under the fundamental sequence.  Zero
        counterexamples over all five populations above, and to three iterated steps.
  (ii)  row 326's index `(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)` is `stdB`, and so is every
        member of its fundamental sequence.
  (iii) **the failing clause is restored.**  Over `popNFB 3 6`, 13 limit indices violate
        `lt (value (fsB t n)) (value t)`; **none of the 13 is `stdB`**, and on the 235
        `stdB` indices the clause holds to `n ≤ 8`, together with strict increase.

WHAT IS PROVED HERE.  `kind_matB` (§4) and `oR_matB` (§5) — the latter carries §60 through
`oRB` and `dict` to the value the table actually holds — and `hzero_supply` plus the INDEX
half of `Hsucc` (§6).

WHAT IS **NOT** CLAIMED.  `stdB t = true` is not proved equivalent to `BMS.Standard`; the
evidence is the 236 422-matrix agreement with the reference implementation, nothing more.
(i) is measured, not proved, so `Hclosed` for this region is still owed.  The VALUE half of
`Hsucc` — `v = plus u one`, `inT v`, `inT u`, `lt u v` — is measured and NOT proved: it
needs `plus`-algebra and an `inT (dict ·)` theorem that this repository does not have.
`Hlim` is not touched. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### 1. 降べきの和の比較

`B` は「和を左に積む」形なので、比較には成分を左から右へ並べ直す必要がある。
`toLA` は蓄積器つきの並べ直し、`cmpS` はその上の辞書式比較 (短い方が小さい)。 -/

/-- 和の成分の重み。停止性の測度。 -/
def sizeL : List (Nat × B) → Nat
  | [] => 0
  | p :: r => sizeB p.2 + 1 + sizeL r

/-- 和の成分を左から右へ (蓄積器つき)。 -/
def toLA : B → List (Nat × B) → List (Nat × B)
  | .nil, acc => acc
  | .nd v r a, acc => toLA r ((v, a) :: acc)

/-- 和の成分を左から右へ。 -/
def toL (t : B) : List (Nat × B) := toLA t []

theorem sizeL_toLA : ∀ (t : B) (acc : List (Nat × B)),
    sizeL (toLA t acc) = sizeB t + sizeL acc := by
  intro t
  induction t with
  | nil => intro acc; show sizeL acc = 0 + sizeL acc; omega
  | nd v r a ihr _ =>
    intro acc
    show sizeL (toLA r ((v, a) :: acc)) = sizeB r + 1 + sizeB a + sizeL acc
    rw [ihr ((v, a) :: acc)]
    show sizeB r + (sizeB a + 1 + sizeL acc) = _
    omega

/-- 成分の重みの合計は節の個数。 -/
theorem sizeL_toL (t : B) : sizeL (toL t) = sizeB t := by
  rw [toL, sizeL_toLA t []]
  rfl

theorem toLA_append : ∀ (t : B) (acc : List (Nat × B)), toLA t acc = toL t ++ acc := by
  intro t
  induction t with
  | nil => intro acc; rfl
  | nd v r a ihr _ =>
    intro acc
    show toLA r ((v, a) :: acc) = toL (B.nd v r a) ++ acc
    rw [ihr ((v, a) :: acc)]
    show toL r ++ ((v, a) :: acc) = (toLA r [(v, a)]) ++ acc
    rw [ihr [(v, a)]]
    rw [List.append_assoc]
    rfl

/-- 節を 1 つ足すと成分が右に 1 つ増える。 -/
theorem toL_nd (v : Nat) (r a : B) : toL (.nd v r a) = toL r ++ [(v, a)] := by
  show toLA r [(v, a)] = _
  rw [toLA_append r [(v, a)]]

/-- **和の比較。** 左から辞書式、成分が尽きた方が小さい。降べきの和の上でだけ意味を持つ。 -/
def cmpS : List (Nat × B) → List (Nat × B) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (u, a) :: xs, (w, b) :: ys =>
      if u < w then .lt
      else if w < u then .gt
      else
        match cmpS (toL a) (toL b) with
        | .eq => cmpS xs ys
        | o => o
termination_by x y => sizeL x + sizeL y
decreasing_by
  · rw [sizeL_toL, sizeL_toL]
    show _ < (sizeB a + 1 + sizeL xs) + (sizeB b + 1 + sizeL ys)
    omega
  · show sizeL xs + sizeL ys < (sizeB a + 1 + sizeL xs) + (sizeB b + 1 + sizeL ys)
    omega

/-- 1 つの節どうしの比較。 -/
def cmpN (u : Nat) (a : B) (w : Nat) (b : B) : Ordering := cmpS [(u, a)] [(w, b)]

/-! ### 2. `stdB`

三つの条件の連言。`nfB` は §19 のもの、`nonIncr` は和が降べきであること、`visOK` は
「段 `v` の節の引数の中に現れる段 `v` の節は、その引数より真に小さい引数を持つ」。 -/

/-- 先頭の 2 つが降べきか。 -/
def hdOK (x : Nat × B) : List (Nat × B) → Bool
  | [] => true
  | y :: _ => !(cmpN x.1 x.2 y.1 y.2 == Ordering.lt)

/-- 成分が左から右へ広義単調減少。 -/
def nonIncrL : List (Nat × B) → Bool
  | [] => true
  | x :: r => hdOK x r && nonIncrL r

/-- 和が降べき。 -/
def nonIncr (t : B) : Bool := nonIncrL (toL t)

/-- **段 `v` の節の許容条件。** 引数 `a` の中を走査し、段が `v` 未満の節で打ち切る。
    段がちょうど `v` の節は、その引数が `a` より真に小さくなければならない。 -/
def visOK (v : Nat) (a : B) : B → Bool
  | .nil => true
  | .nd u r c =>
      visOK v a r &&
      (if u < v then true
       else (if u == v then cmpS (toL c) (toL a) == Ordering.lt else true) && visOK v a c)

/-- すべての節での条件。 -/
def stdIn : B → Bool
  | .nil => true
  | .nd v r c => stdIn r && nonIncr c && visOK v c c && stdIn c

/-- **BMS 標準性の添字側の判定。** `~/proofs/yaBMS/c/bms -s` と 236 422 個で一致。 -/
def stdB (t : B) : Bool := nfB t && nonIncr t && stdIn t

/-! ### 3. 測定 (凍結)

`bms -s` の判定を Lean のリテラルとして凍結する。1 行目は `popNFB 3 6` の 670 個ぶんの
判定そのもの、以下は各母集団の標準行列の個数。すべて参照実装の出力。 -/

/-- `~/proofs/yaBMS/c/bms -s` を `popNFB 3 6` の 670 個の行列に順に当てた結果。 -/
def bmsStd670 : String :=
  "1111110111011001111101101011001110000101011100000101001011001111100010110000000001011001101110110011111011010110010001100011001000010011101100000000010110101100000100100100000000000000100001000000110110101100001010111010000101011100000111110000000000001000010100001001101110000000000000000000000000010000000000001000010000000100001110000000111101111100000000000000010100101100111100110011110000111011000000001100110011111100000000001000100000100010110000101110111000000010001011000000000000000000000000000000000000000000000000000000000000000100001000000000000101100111110001111000000000011011010110011100001010111000001010010110011111000101100000000010110011011101100111"

#guard bmsStd670.length == 670
#guard (bmsStd670.toList.filter (· == '1')).length == 235
-- **`stdB` は参照実装そのもの。**
#guard (String.join ((popNFB 3 6).map fun t => if stdB t then "1" else "0")) == bmsStd670
-- 参照実装が数えた標準行列の個数と、`stdB` が数えた個数。
#guard ((enumB 3 6).filter stdB).length == 1105
#guard ((enumB 4 5).filter stdB).length == 250
#guard ((enumB 3 7).filter stdB).length == 5507
#guard ((enumB 4 6).filter stdB).length == 1263

/-- 標準な添字の母集団。 -/
def popS (L n : Nat) : List B := (popNFB L n).filter stdB

#guard (popS 3 6).length == 235
#guard (popS 4 6).length == 250

-- (i) 基本列で閉じる。**測定のみ。**
#guard (enumB 3 6).all fun t => !(stdB t) || (List.range 6).all fun n => stdB (fsB t n)
#guard (enumB 4 5).all fun t => !(stdB t) || (List.range 6).all fun n => stdB (fsB t n)
#guard (enumB 3 7).all fun t => !(stdB t) || (List.range 4).all fun n => stdB (fsB t n)
#guard (enumB 4 6).all fun t => !(stdB t) || (List.range 4).all fun n => stdB (fsB t n)
-- 2 段、3 段でも。
#guard (popNFB 3 6).all fun t => !(stdB t) ||
  (List.range 4).all fun n => (List.range 4).all fun m => stdB (fsB (fsB t n) m)
#guard (popNFB 3 6).all fun t => !(stdB t) ||
  (List.range 3).all fun n => (List.range 3).all fun m => (List.range 3).all fun k =>
    stdB (fsB (fsB (fsB t n) m) k)

-- 表そのもの。参照実装は `popB` の 877 個と `wideRows` の 52 個をすべて標準と呼び、
-- `stdB` もすべて受け入れる。`popB` は最大 47 列で、上の列挙とは母集団の形が違う。
#guard popB.length == 877
#guard popB.all fun S => match decodeB S with | none => false | some t => stdB t
#guard wideRows.all fun M => match decodeB M with | none => false | some t => stdB t
#guard popB.all fun S => match decodeB S with
  | none => false | some t => (List.range 5).all fun n => stdB (fsB t n)

-- (ii) 326 行目の添字。
#guard (decodeB [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]).isSome
#guard match decodeB [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]] with
  | none => false
  | some t => nfB t && stdB t && (List.range 6).all fun n => stdB (fsB t n)

/-- 添字の値。`oR` と同じ `1 +` の約束を持つ (空行列は 0)。 -/
def vOf : B → TM.Term
  | .nil => TM.Term.zero
  | t@(.nd _ _ _) => TM.Term.plus TM.Term.one (Trans.Dict.dict (bVal t))

/-- 添字が自分で読む種別。 -/
def kindB : B → BMS.Kind
  | .nil => .zero
  | .nd v _ .nil => if v == 0 then .succ else .lim
  | .nd _ _ _ => .lim

-- `vOf` は表の値そのもの (§5 が定理にする)。
#guard (popNFB 3 6).all fun t => Trans.Recal.oR (matB t 0) == some (vOf t)

-- (iii) **落ちていた極限の条項が戻る。** `nfB` だけでは 13 個が落ち、そのどれも `stdB` でない。
#guard ((popNFB 3 6).filter fun t => kindB t == BMS.Kind.lim &&
  !((List.range 5).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf t))).length == 13
#guard ((popNFB 3 6).filter fun t => kindB t == BMS.Kind.lim && stdB t &&
  !((List.range 5).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf t))).length == 0
-- 標準な添字の上では `n ≤ 8` まで成り立ち、真に増える。**測定のみ。**
#guard (popS 3 6).all fun t => !(kindB t == BMS.Kind.lim) ||
  (List.range 9).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf t)
#guard (popS 4 6).all fun t => !(kindB t == BMS.Kind.lim) ||
  (List.range 6).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf t)
#guard (popS 3 6).all fun t => !(kindB t == BMS.Kind.lim) ||
  (List.range 8).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf (fsB t (n+1)))
#guard (popS 4 6).all fun t => !(kindB t == BMS.Kind.lim) ||
  (List.range 5).all fun n => TM.Term.lt (vOf (fsB t n)) (vOf (fsB t (n+1)))
-- 3 つの最小の反例は、どれも `stdB` でない。
#guard (decodeB [[0,0],[1,0],[2,1],[1,1]]).isSome
#guard match decodeB [[0,0],[1,0],[2,1],[1,1]] with
  | none => false | some t => nfB t && !(stdB t)
#guard match decodeB [[0,0],[1,0],[2,0],[3,1],[2,1]] with
  | none => false | some t => nfB t && !(stdB t)
#guard match decodeB [[0,0],[1,1],[2,1],[3,2],[2,2]] with
  | none => false | some t => nfB t && !(stdB t)
-- Buchholz そのものの条件 (段が `v` 以上のすべての節を縛る) は**強すぎる**。
-- 対角 `(0,0)(1,1)(2,2)` を含む 75 個を落としてしまう。その最小のもの。
#guard match decodeB [[0,0],[1,1],[2,2]] with
  | none => false | some t => stdB t
-- `Hsucc` の値の側。**測定のみ、証明されていない。**
#guard (popS 3 6).all fun t => !(kindB t == BMS.Kind.succ) ||
  (vOf t == TM.Term.plus (vOf (fsB t 0)) TM.Term.one)
#guard (popS 3 6).all fun t => !(kindB t == BMS.Kind.succ) ||
  (List.range 5).all fun n => fsB t n == fsB t 0
#guard (popS 3 6).all fun t => TM.Term.inT (vOf t)
#guard (popS 4 6).all fun t => TM.Term.inT (vOf t)
-- `CNV` は 235 個中 150 個。`certIn_region_cnv` は最上位の値にしか要らない。
#guard ((popS 3 6).filter fun t => Evidence.WF.CNV (vOf t)).length == 150
-- 値は添字を分ける。
#guard ((popS 3 6).map vOf).eraseDups.length == 235

/-! ### 4. 種別

`BMS.lnz` は列の**最後の**非零行なので、種別が後続になるのは最後の列が `[0,0]` の
ときちょうど — つまり最上位に段 0 の葉が来たとき。仮定は要らない。 -/

/-- 空でない添字の行列の最後の列。 -/
theorem matB_getLast? (a : B) (ha : a ≠ .nil) (d : Nat) :
    (matB a d).getLast? = some [d + lastDep a, lastLvl a] := by
  have h := matB_last a ha d
  calc (matB a d).getLast?
      = ((matB a d).dropLast ++ [[d + lastDep a, lastLvl a]]).getLast? := by rw [← h]
    _ = some [d + lastDep a, lastLvl a] := getLast?_append_ne _ _ (by simp)

/-- **種別は添字が決める。** 仮定は要らない。 -/
theorem kind_matB (t : B) : BMS.kind (matB t 0) = kindB t := by
  cases t with
  | nil => rfl
  | nd v r a =>
    cases a with
    | nil =>
      show (match (matB r 0 ++ ([0, v] :: matB B.nil 1)).getLast? with
        | none => BMS.Kind.zero
        | some L => match lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
        = (if v == 0 then BMS.Kind.succ else BMS.Kind.lim)
      rw [show ([0, v] :: matB B.nil 1) = [[0, v]] from rfl,
        getLast?_append_ne _ _ (by simp)]
      show (match lnz [0, v] with | none => BMS.Kind.succ | some _ => BMS.Kind.lim) = _
      rw [lnz_pair]
      cases v with
      | zero => rfl
      | succ k => rw [if_pos (by omega)]; rfl
    | nd w b c =>
      have ha : (B.nd w b c) ≠ .nil := by intro h; exact B.noConfusion h
      have hne : matB (B.nd w b c) 1 ≠ [] := by
        intro h
        have := matB_len_pos (B.nd w b c) 1 ha
        rw [h] at this
        exact absurd this (by simp)
      show (match (matB r 0 ++ ([0, v] :: matB (B.nd w b c) 1)).getLast? with
        | none => BMS.Kind.zero
        | some L => match lnz L with | none => BMS.Kind.succ | some _ => BMS.Kind.lim)
        = BMS.Kind.lim
      rw [getLast?_append_ne _ _ (by simp), List.getLast?_cons_of_ne_nil hne,
        matB_getLast? (B.nd w b c) ha 1]
      show (match lnz [1 + lastDep (B.nd w b c), lastLvl (B.nd w b c)] with
        | none => BMS.Kind.succ | some _ => BMS.Kind.lim) = _
      rw [lnz_pair]
      cases hl : lastLvl (B.nd w b c) with
      | zero => rw [if_neg (by omega), if_pos (by omega)]
      | succ _ => rw [if_pos (by omega)]

/-- 種別 0 の添字は `nil` だけ。 -/
theorem kindB_nd_nil (v : Nat) (r : B) :
    kindB (.nd v r .nil) = (if v == 0 then BMS.Kind.succ else BMS.Kind.lim) := rfl

theorem kindB_zero : ∀ (t : B), kindB t = BMS.Kind.zero → t = .nil := by
  intro t
  cases t with
  | nil => intro _; rfl
  | nd v r a =>
    cases a with
    | nil =>
      intro h
      rw [kindB_nd_nil] at h
      cases hv : (v == 0) with
      | true => rw [hv] at h; exact BMS.Kind.noConfusion h
      | false => rw [hv] at h; exact BMS.Kind.noConfusion h
    | nd w b c => intro h; exact BMS.Kind.noConfusion h

/-- 種別後続の添字は `nd 0 r nil`。 -/
theorem kindB_succ : ∀ (t : B), kindB t = BMS.Kind.succ → ∃ r, t = .nd 0 r .nil := by
  intro t
  cases t with
  | nil => intro h; exact BMS.Kind.noConfusion h
  | nd v r a =>
    cases a with
    | nil =>
      intro h
      rw [kindB_nd_nil] at h
      cases hv : (v == 0) with
      | true =>
        refine ⟨r, ?_⟩
        rw [show v = 0 from (beq_iff_eq (a := v) (b := 0)).mp hv]
      | false =>
        rw [hv] at h
        exact BMS.Kind.noConfusion h
    | nd w b c => intro h; exact BMS.Kind.noConfusion h

/-! ### 5. `oR`

§60 の `transPort_bVal` を `oRB` と `dict` を通して表の値まで運ぶ。`oR` は空行列だけを
特別扱いして `0` を返すので、添字側の値 `vOf` も同じ特別扱いを持つ。 -/

/-- **`oR` は `bVal` の辞書引きに `1 +` を付けたもの。** -/
theorem oR_matB (t : B) (hnf : nfB t = true) (hne : t ≠ .nil) :
    Trans.Recal.oR (matB t 0)
      = some (TM.Term.plus TM.Term.one (Trans.Dict.dict (bVal t))) := by
  have h1 : (matB t 0).isEmpty = false := by
    have hp := matB_len_pos t 0 hne
    cases hm : matB t 0 with
    | nil => rw [hm] at hp; exact absurd hp (by simp)
    | cons c cs => rfl
  show (if (matB t 0).isEmpty = true then some TM.Term.zero
        else (Trans.Recal.oRB (matB t 0)).map
          (fun x => TM.Term.plus TM.Term.one (Trans.Dict.dict x))) = _
  rw [if_neg (by rw [h1]; exact fun h => Bool.noConfusion h)]
  show ((ofMatrix (matB t 0)).map transPort).map
      (fun x => TM.Term.plus TM.Term.one (Trans.Dict.dict x)) = _
  rw [ofMatrix_matB t 0 hne]
  show some (TM.Term.plus TM.Term.one (Trans.Dict.dict (transPort (psM (matB t 0))))) = _
  rw [transPort_bVal t hnf hne]

/-- **`vOf` は表の値。** 空添字も込めて 1 本の等式。 -/
theorem oR_vOf (t : B) (hnf : nfB t = true) : Trans.Recal.oR (matB t 0) = some (vOf t) := by
  cases t with
  | nil => rfl
  | nd v r a =>
    have hne : (B.nd v r a) ≠ .nil := by intro h; exact B.noConfusion h
    rw [oR_matB (B.nd v r a) hnf hne]
    rfl

/-! ### 6. 領域と、最初の 2 つの供給

`RegS`/`ValS` は `certIn_region` の 2 つの引数。`Evidence/RegionV.lean` §12 の形をそのまま
一般化した添字に載せ替えたもの。`Hzero` は定理、`Hsucc` は**添字の側だけ**が定理。 -/

/-- 領域: 標準な添字の行列。 -/
def RegS (S : BMS.Matrix) : Prop := ∃ t : B, stdB t = true ∧ S = matB t 0

/-- その上の値付け。 -/
def ValS (S : BMS.Matrix) (v : TM.Term) : Prop :=
  ∃ t : B, stdB t = true ∧ S = matB t 0 ∧ v = vOf t

theorem stdB_nil : stdB .nil = true := rfl

theorem nfB_of_stdB (t : B) (h : stdB t = true) : nfB t = true :=
  ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).1

theorem nonIncr_of_stdB (t : B) (h : stdB t = true) : nonIncr t = true :=
  ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2

theorem stdIn_of_stdB (t : B) (h : stdB t = true) : stdIn t = true :=
  ((Bool.and_eq_true _ _).mp h).2

/-- 成分を 1 つ右に足しても、左側の降べきは残る。 -/
theorem nonIncrL_cons (x : Nat × B) (r : List (Nat × B)) :
    nonIncrL (x :: r) = (hdOK x r && nonIncrL r) := rfl

theorem nonIncrL_dropLast : ∀ (l : List (Nat × B)) (x : Nat × B),
    nonIncrL (l ++ [x]) = true → nonIncrL l = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro x h
    rw [show (a :: l) ++ [x] = a :: (l ++ [x]) from rfl, nonIncrL_cons] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    rw [nonIncrL_cons, ih x h2, Bool.and_true]
    cases l with
    | nil => rfl
    | cons b l' => exact h1

/-- **`stdB` は最後の節を落としても残る (段 0 の葉のとき)。** -/
theorem stdB_pred (r : B) (h : stdB (.nd 0 r .nil) = true) : stdB r = true := by
  have hnf : nfB (.nd 0 r .nil) = true := nfB_of_stdB _ h
  have hni : nonIncr (.nd 0 r .nil) = true := nonIncr_of_stdB _ h
  have hin : stdIn (.nd 0 r .nil) = true := stdIn_of_stdB _ h
  have h1 : nfB r = true := ((nfLe_nd_iff 0 0 r .nil).mp hnf).2.1
  have h2 : nonIncr r = true := by
    have hni' : nonIncrL (toL (B.nd 0 r .nil)) = true := hni
    rw [toL_nd 0 r .nil] at hni'
    exact nonIncrL_dropLast (toL r) (0, .nil) hni'
  have h3 : stdIn r = true := by
    have : (stdIn r && nonIncr .nil && visOK 0 .nil .nil && stdIn .nil) = true := hin
    exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
      ((Bool.and_eq_true _ _).mp this).1).1).1
  show (nfB r && nonIncr r && stdIn r) = true
  rw [h1, h2, h3]
  rfl

/-- **`Hzero`。** 種別 0 の行列は添字 `nil` から来て、値は `0`。 -/
theorem hzeroS_supply : ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v →
    BMS.kind S = BMS.Kind.zero → v = TM.Term.zero := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  rw [kindB_zero t hk]
  rfl

/-- **`Hsucc` の添字の側。** 種別後続の行列は `nd 0 r nil` から来て、その展開は `n` に
    よらず `matB r 0`、値は `vOf r`。値の等式 `v = plus (vOf r) one` は**測定のみ**。 -/
theorem hsuccS_index : ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v →
    BMS.kind S = BMS.Kind.succ →
    ∃ r : B, v = vOf (.nd 0 r .nil) ∧ stdB r = true
             ∧ ∀ n, BMS.expand S n = matB r 0 ∧ ValS (BMS.expand S n) (vOf r) := by
  rintro S v _ ⟨t, hstd, rfl, rfl⟩ hk
  rw [kind_matB t] at hk
  obtain ⟨r, rfl⟩ := kindB_succ t hk
  have hr : stdB r = true := stdB_pred r hstd
  have hnf : nfB (B.nd 0 r .nil) = true := nfB_of_stdB _ hstd
  have htop : topOKB (B.nd 0 r .nil) = true := topOKB_of_nfB _ hnf
  have hexp : ∀ n, BMS.expand (matB (B.nd 0 r .nil) 0) n = matB r 0 := by
    intro n
    show (BMS.expand? (matB (B.nd 0 r .nil) 0) n).getD [] = _
    rw [expand_matB (B.nd 0 r .nil) htop (by intro h; exact B.noConfusion h) n]
    rfl
  exact ⟨r, rfl, hr, fun n => ⟨hexp n, ⟨r, hr, (hexp n).symm ▸ rfl, rfl⟩⟩⟩

/-! ### 公理の確認 -/

end

/-! ## §62 `stdB` IS CLOSED UNDER THE FUNDAMENTAL SEQUENCE

§61 found `stdB` — `nfB && nonIncr && stdIn` — measured that it agrees with the C reference
implementation on 236 422 matrices, and left its closure under `fsB` as a measurement.  §62
proves it, and with it `Hclosed` for the narrowed region:

    stdB_fsB        stdB t → stdB (fsB t n)
    hclosedS_supply ∀ S, RegS S → ∀ n, RegS (BMS.expand S n)

WHY IT IS NOT A WALK OVER THE OPERATORS.  `nfB` is LOCAL and §19 pushed it through `appB`,
`plugB`, `repNode`, `repB`, `iterD`, `rwB` one lemma each.  `nonIncr` and `stdIn` are not:
`nonIncr` compares a node's argument against its neighbour and `visOK` compares it against the
WHOLE sum it sits in.  So the first thing §62 needs is an ORDER on `cmpS`, and there was none.

    §62.1  cmpS_refl / cmpS_eq_imp / cmpS_swap / cmpS_trans   `cmpS` is a linear order
    §62.2  cmpS_lt_append / cmpS_append_left                  a common prefix is inert
           cmpS_ctx        a term smaller than the prefix cannot see past it
           cmpS_split      `x < p ++ q` splits into three exhaustive shapes — the workhorse
           cmpS_lt_snoc_zero  `(0,0)` is the least component, so it can be dropped
    §62.4  visOK_iff       `visOK v a s` is `∀ c ∈ vArgs v s, c < a`, and `vArgs v s` is a
                           list of SUBTERMS (`vArgs_size`), which is what makes the size
                           bounds in the transfers usable

THE TWO TRANSFERS.  Every step of the closure is one of exactly two shapes, and both have to
be proved for `repB` (§62.6–§62.7) and again for `plugB` (§62.8):

    the reference STAYS PUT   `visOK v ref a → visOK v ref (op a)`.  Every argument the
                              operator creates is BELOW the one it replaces (`repB_lt`,
                              `plugB_lt`, `GG_lt`), so transitivity alone does it.
    the reference MOVES       a subterm of `op a` that was below `a` is below `op a`
                              (`C1_repB`, `C1_GG`).  `cmpS_split` leaves three cases and the
                              size bound `sizeB x < sizeB (op a)` kills two of them.

`visOK_self_repB` / `visOK_self_GG` / `visOK_self_rwB` close the loop: the self-referential
`visOK v (op a) (op a)` is the first transfer followed by the second, applied to each element
of `vArgs`.

THE ONE PLACE THE NAIVE INDUCTION FAILS, and it is worth recording because the first attempt
died on it.  `C1_repB`'s statement is FALSE for `plugB`: with `a = ψ₁(0)`, `x = ψ₀(ψ₁(0))`,
`n = 2` one has `x < a`, `sizeB x < sizeB (plugB a (iterD 0 a 2))` and yet
`x > plugB a (iterD 0 a 2)` (frozen as a `#guard` in §62.11).  What is missing is
`visOK (w-1) x x`, and — this is the point — it does NOT propagate as the induction descends
`a`'s last spine, because that descent passes through nodes of level `≥ w > w-1`.  The fix is
to hold the REFERENCE fixed at the top argument `a₀` while the scan descends
(`C1_plugB_cons`'s `∀ z' ∈ vArgs v' x, z' < a₀`), and to run an OUTER induction on the
nesting depth of `iterD`, whose base case is killed by the size bound alone
(`C1_plugB_nil`).  `lowAnc_lvl` is the only place `nfB` is used: it says the nearest ancestor
of lower level has level EXACTLY `w-1`, which is what makes `u < w → u ≤ v'` available at the
bottom of the descent.

WHAT IS **NOT** CLAIMED.  `stdB t = true` is still not proved equivalent to `BMS.Standard`;
§61's 236 422-matrix agreement with the reference is the only evidence for that, and §62 adds
none.  `Hlim` and the VALUE half of `Hsucc` are untouched.  Task 3 of the brief —
`dict (bplus x y) = plus (dict x) (dict y)` — is measured (§62.11) and NOT proved: it needs
`plus` to be associative, and the repository's only associativity, `Evidence.CNVOps.plus_assoc`,
requires `CNV`, which only 150 of the 235 standard values of `popNFB 3 6` satisfy.  The general
route needs a `plus_assoc` built on `Evidence.WF.lt_trans_inT` / `lt_trichotomy_inT` plus an
`inT (dict ·)` theorem, and neither exists. -/

section
open Trans.Recal
open Trans.Dict (BT)

/-! ### §62.1 `cmpS` の式と、それが線形順序であること -/

theorem cmpS_nil_nil : cmpS [] [] = .eq := by rw [cmpS]
theorem cmpS_nil_cons (y : Nat × B) (ys : List (Nat × B)) : cmpS [] (y :: ys) = .lt := by
  rw [cmpS]
theorem cmpS_cons_nil (x : Nat × B) (xs : List (Nat × B)) : cmpS (x :: xs) [] = .gt := by
  rw [cmpS]
theorem cmpS_cons (u : Nat) (a : B) (xs : List (Nat × B)) (w : Nat) (b : B)
    (ys : List (Nat × B)) :
    cmpS ((u, a) :: xs) ((w, b) :: ys)
      = (if u < w then .lt else if w < u then .gt else
          match cmpS (toL a) (toL b) with | .eq => cmpS xs ys | o => o) := by
  rw [cmpS]

/-! #### リストの補題と `toL` の単射性 -/

theorem app_sing_ne_nil {α : Type} : ∀ (l : List α) (x : α), l ++ [x] ≠ []
  | [], x => List.cons_ne_nil x []
  | a :: l', x => List.cons_ne_nil a (l' ++ [x])

theorem app_sing_inj {α : Type} : ∀ (l1 l2 : List α) (x y : α),
    l1 ++ [x] = l2 ++ [y] → l1 = l2 ∧ x = y
  | [], [], x, y, h => ⟨rfl, by injection h⟩
  | [], b :: l2', x, y, h => by
      exfalso
      injection h with _ h2
      exact app_sing_ne_nil l2' y h2.symm
  | a :: l1', [], x, y, h => by
      exfalso
      injection h with _ h2
      exact app_sing_ne_nil l1' x h2
  | a :: l1', b :: l2', x, y, h => by
      injection h with h1 h2
      obtain ⟨h3, h4⟩ := app_sing_inj l1' l2' x y h2
      exact ⟨by rw [h1, h3], h4⟩

theorem toL_nil : toL (.nil : B) = [] := rfl

theorem toL_ne_nil (v : Nat) (r a : B) : toL (.nd v r a) ≠ [] := by
  rw [toL_nd]
  exact app_sing_ne_nil (toL r) (v, a)

/-- `toL` は単射。 -/
theorem toL_inj : ∀ (s t : B), toL s = toL t → s = t := by
  intro s
  induction s with
  | nil =>
    intro t h
    cases t with
    | nil => rfl
    | nd w u b => exact absurd h.symm (toL_ne_nil w u b)
  | nd v r a ihr _ =>
    intro t h
    cases t with
    | nil => exact absurd h (toL_ne_nil v r a)
    | nd w u b =>
      rw [toL_nd, toL_nd] at h
      obtain ⟨h1, h2⟩ := app_sing_inj _ _ _ _ h
      injection h2 with h3 h4
      rw [ihr u h1, h3, h4]


/-! #### 反射・等号・推移 -/

theorem sizeL_cons (u : Nat) (a : B) (xs : List (Nat × B)) :
    sizeL ((u, a) :: xs) = sizeB a + 1 + sizeL xs := rfl

theorem cmpS_refl : ∀ (x : List (Nat × B)), cmpS x x = .eq
  | [] => cmpS_nil_nil
  | (u, a) :: xs => by
      rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
        cmpS_refl (toL a)]
      exact cmpS_refl xs
termination_by x => sizeL x
decreasing_by
  · rw [sizeL_toL, sizeL_cons]; omega
  · rw [sizeL_cons]; omega

/-- `eq` は等しさ。 -/
theorem cmpS_eq_imp : ∀ (x y : List (Nat × B)), cmpS x y = .eq → x = y
  | [], [], _ => rfl
  | [], y :: ys, h => by rw [cmpS_nil_cons] at h; exact Ordering.noConfusion h
  | x :: xs, [], h => by rw [cmpS_cons_nil] at h; exact Ordering.noConfusion h
  | (u, a) :: xs, (w, b) :: ys, h => by
      rw [cmpS_cons] at h
      have huw : u = w := by
        by_cases h1 : u < w
        · rw [if_pos h1] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
        · rw [if_neg h1] at h
          by_cases h2 : w < u
          · rw [if_pos h2] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
          · omega
      subst huw
      rw [if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u)] at h
      cases hab : cmpS (toL a) (toL b) with
      | lt => rw [hab] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
      | gt => rw [hab] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
      | eq =>
        rw [hab] at h
        have hb : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
        have hx : xs = ys := cmpS_eq_imp xs ys h
        rw [hb, hx]
termination_by x y => sizeL x + sizeL y
decreasing_by
  · rw [sizeL_toL, sizeL_toL, sizeL_cons, sizeL_cons]; omega
  · rw [sizeL_cons, sizeL_cons]; omega

/-- 推移律。 -/
theorem cmpS_trans : ∀ (x y z : List (Nat × B)),
    cmpS x y = .lt → cmpS y z = .lt → cmpS x z = .lt
  | [], [], _, h1, _ => by rw [cmpS_nil_nil] at h1; exact Ordering.noConfusion h1
  | [], _ :: _, [], _, h2 => by rw [cmpS_cons_nil] at h2; exact Ordering.noConfusion h2
  | [], _ :: _, _ :: _, _, _ => by rw [cmpS_nil_cons]
  | _ :: _, [], _, h1, _ => by rw [cmpS_cons_nil] at h1; exact Ordering.noConfusion h1
  | _ :: _, _ :: _, [], _, h2 => by rw [cmpS_cons_nil] at h2; exact Ordering.noConfusion h2
  | (u, a) :: xs, (w, b) :: ys, (p, c) :: zs, h1, h2 => by
      rw [cmpS_cons] at h1
      rw [cmpS_cons] at h2
      rw [cmpS_cons]
      have hpw : ¬ (p < w) := by
        intro hc
        rw [if_neg (by omega), if_pos hc] at h2
        exact Ordering.noConfusion h2
      by_cases huw : u < w
      · rw [if_pos (show u < p by omega)]
      · rw [if_neg huw] at h1
        have hwu : ¬ (w < u) := by
          intro hc
          rw [if_pos hc] at h1
          exact Ordering.noConfusion h1
        rw [if_neg hwu] at h1
        have hu : u = w := by omega
        subst hu
        by_cases hup : u < p
        · rw [if_pos hup]
        · rw [if_neg hup] at h2
          have hu2 : u = p := by omega
          subst hu2
          rw [if_neg (show ¬ (u < u) by omega)] at h2
          rw [if_neg (show ¬ (u < u) by omega), if_neg (show ¬ (u < u) by omega)]
          cases hab : cmpS (toL a) (toL b) with
          | gt => rw [hab] at h1; exact Ordering.noConfusion h1
          | lt =>
            cases hbc : cmpS (toL b) (toL c) with
            | gt =>
              rw [hbc] at h2
              exact Ordering.noConfusion (show Ordering.gt = Ordering.lt from h2)
            | lt =>
              rw [cmpS_trans (toL a) (toL b) (toL c) hab hbc]
            | eq =>
              have : b = c := toL_inj b c (cmpS_eq_imp (toL b) (toL c) hbc)
              subst this
              rw [hab]
          | eq =>
            have hbe : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
            subst hbe
            rw [hab] at h1
            cases hbc : cmpS (toL a) (toL c) with
            | gt =>
              rw [hbc] at h2
              exact Ordering.noConfusion (show Ordering.gt = Ordering.lt from h2)
            | lt => rfl
            | eq =>
              rw [hbc] at h2
              exact cmpS_trans xs ys zs h1 h2
termination_by x y z => sizeL x + sizeL y + sizeL z
decreasing_by
  · rw [sizeL_toL, sizeL_toL, sizeL_toL, sizeL_cons, sizeL_cons, sizeL_cons]; omega
  · rw [sizeL_cons, sizeL_cons, sizeL_cons]; omega


/-! ### §62.2 連結と文脈 -/

theorem sizeL_append : ∀ (l1 l2 : List (Nat × B)), sizeL (l1 ++ l2) = sizeL l1 + sizeL l2
  | [], l2 => by show sizeL l2 = 0 + sizeL l2; omega
  | (u, a) :: l1, l2 => by
      show sizeB a + 1 + sizeL (l1 ++ l2) = (sizeB a + 1 + sizeL l1) + sizeL l2
      rw [sizeL_append l1 l2]
      omega

theorem cmpS_nil_right_ne_lt : ∀ (x : List (Nat × B)), cmpS x [] ≠ .lt
  | [] => by rw [cmpS_nil_nil]; intro hc; exact Ordering.noConfusion hc
  | y :: ys => by rw [cmpS_cons_nil]; intro hc; exact Ordering.noConfusion hc

/-- 右に足しても `lt` は保たれる。 -/
theorem cmpS_lt_append : ∀ (x p q : List (Nat × B)), cmpS x p = .lt → cmpS x (p ++ q) = .lt
  | [], [], q, h => by rw [cmpS_nil_nil] at h; exact Ordering.noConfusion h
  | [], y :: ys, q, _ => cmpS_nil_cons y (ys ++ q)
  | x :: xs, [], q, h => by rw [cmpS_cons_nil] at h; exact Ordering.noConfusion h
  | (u, a) :: xs, (w, b) :: ps, q, h => by
      rw [cmpS_cons] at h
      show cmpS ((u, a) :: xs) ((w, b) :: (ps ++ q)) = .lt
      rw [cmpS_cons]
      by_cases h1 : u < w
      · rw [if_pos h1]
      · rw [if_neg h1] at h ⊢
        by_cases h2 : w < u
        · rw [if_pos h2] at h; exact Ordering.noConfusion h
        · rw [if_neg h2] at h ⊢
          cases hab : cmpS (toL a) (toL b) with
          | lt => rfl
          | gt => rw [hab] at h; exact Ordering.noConfusion h
          | eq =>
            rw [hab] at h
            exact cmpS_lt_append xs ps q h
termination_by x p _ => sizeL x + sizeL p
decreasing_by
  · rw [sizeL_cons, sizeL_cons]; omega

/-- 共通の接頭辞は無視できる。 -/
theorem cmpS_append_left : ∀ (p q1 q2 : List (Nat × B)),
    cmpS (p ++ q1) (p ++ q2) = cmpS q1 q2
  | [], q1, q2 => rfl
  | (w, b) :: ps, q1, q2 => by
      show cmpS ((w, b) :: (ps ++ q1)) ((w, b) :: (ps ++ q2)) = _
      rw [cmpS_cons, if_neg (Nat.lt_irrefl w), if_neg (Nat.lt_irrefl w), cmpS_refl (toL b)]
      exact cmpS_append_left ps q1 q2

/-- 真の接頭辞は小さい。 -/
theorem cmpS_lt_self_append (p q : List (Nat × B)) (hq : q ≠ []) : cmpS p (p ++ q) = .lt := by
  have := cmpS_append_left p [] q
  rw [List.append_nil] at this
  rw [this]
  cases q with
  | nil => exact absurd rfl hq
  | cons y ys => rw [cmpS_nil_cons]

/-- **文脈独立性。** `x` が接頭辞より真に小さいなら、その先は比較に効かない。 -/
theorem cmpS_ctx : ∀ (x p q : List (Nat × B)), sizeL x < sizeL p →
    cmpS x (p ++ q) = cmpS x p
  | x, [], q, h => by
      exact absurd h (by rw [show sizeL ([] : List (Nat × B)) = 0 from rfl]; omega)
  | [], (w, b) :: ps, q, _ => by
      show cmpS [] ((w, b) :: (ps ++ q)) = _
      rw [cmpS_nil_cons, cmpS_nil_cons]
  | (u, a) :: xs, (w, b) :: ps, q, h => by
      show cmpS ((u, a) :: xs) ((w, b) :: (ps ++ q)) = _
      rw [cmpS_cons, cmpS_cons]
      by_cases h1 : u < w
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : w < u
        · rw [if_pos h2, if_pos h2]
        · rw [if_neg h2, if_neg h2]
          cases hab : cmpS (toL a) (toL b) with
          | lt => rfl
          | gt => rfl
          | eq =>
            have hb : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
            subst hb
            refine cmpS_ctx xs ps q ?_
            rw [sizeL_cons, sizeL_cons] at h
            omega
termination_by x p _ _ => sizeL x + sizeL p
decreasing_by
  · rw [sizeL_cons, sizeL_cons]; omega

/-- **末尾の `ψ₀(0)` を落とす。** `(0, nil)` は最小の成分なので、これを付けた和より
    小さいものは、付ける前より小さいか、ちょうど等しい。 -/
theorem cmpS_lt_snoc_zero : ∀ (x p : List (Nat × B)),
    cmpS x (p ++ [(0, (.nil : B))]) = .lt → cmpS x p = .lt ∨ x = p
  | [], [], _ => Or.inr rfl
  | (u, a) :: xs, [], h => by
      exfalso
      have h' : cmpS ((u, a) :: xs) [(0, (.nil : B))] = .lt := h
      rw [cmpS_cons] at h'
      rw [if_neg (show ¬ (u < 0) by omega)] at h'
      by_cases h1 : 0 < u
      · rw [if_pos h1] at h'; exact Ordering.noConfusion h'
      · rw [if_neg h1] at h'
        cases haa : cmpS (toL a) (toL (.nil : B)) with
        | lt => exact cmpS_nil_right_ne_lt (toL a) haa
        | gt => rw [haa] at h'; exact Ordering.noConfusion h'
        | eq =>
          rw [haa] at h'
          exact cmpS_nil_right_ne_lt xs h'
  | [], (w, b) :: ps, _ => Or.inl (cmpS_nil_cons (w, b) ps)
  | (u, a) :: xs, (w, b) :: ps, h => by
      have h' : cmpS ((u, a) :: xs) ((w, b) :: (ps ++ [(0, (.nil : B))])) = .lt := h
      rw [cmpS_cons] at h'
      rw [cmpS_cons]
      by_cases h1 : u < w
      · rw [if_pos h1]; exact Or.inl rfl
      · rw [if_neg h1] at h' ⊢
        by_cases h2 : w < u
        · rw [if_pos h2] at h'; exact Ordering.noConfusion h'
        · rw [if_neg h2] at h' ⊢
          cases hab : cmpS (toL a) (toL b) with
          | lt => exact Or.inl rfl
          | gt => rw [hab] at h'; exact Ordering.noConfusion h'
          | eq =>
            rw [hab] at h'
            have hb : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
            subst hb
            rcases cmpS_lt_snoc_zero xs ps h' with hl | he
            · exact Or.inl hl
            · subst he
              have huw : u = w := by omega
              subst huw
              exact Or.inr rfl
termination_by x p => sizeL x + sizeL p
decreasing_by
  · rw [sizeL_cons, sizeL_cons]; omega


/-! #### 接頭辞による三分 -/

/-- **`p ++ q` より小さいものの三分。** `p` より小さいか、`p` そのものか、`p` を接頭辞に持つ。 -/
theorem cmpS_split : ∀ (x p q : List (Nat × B)), cmpS x (p ++ q) = .lt →
    cmpS x p = .lt ∨ x = p ∨ ∃ x', x' ≠ [] ∧ x = p ++ x' ∧ cmpS x' q = .lt
  | [], [], q, h => Or.inr (Or.inl rfl)
  | y :: ys, [], q, h => Or.inr (Or.inr ⟨y :: ys, List.cons_ne_nil y ys, rfl, h⟩)
  | [], (w, b) :: ps, q, _ => Or.inl (cmpS_nil_cons (w, b) ps)
  | (u, a) :: xs, (w, b) :: ps, q, h => by
      have h' : cmpS ((u, a) :: xs) ((w, b) :: (ps ++ q)) = .lt := h
      rw [cmpS_cons] at h'
      by_cases h1 : u < w
      · exact Or.inl (by rw [cmpS_cons, if_pos h1])
      · rw [if_neg h1] at h'
        by_cases h2 : w < u
        · rw [if_pos h2] at h'; exact Ordering.noConfusion h'
        · rw [if_neg h2] at h'
          cases hab : cmpS (toL a) (toL b) with
          | lt => exact Or.inl (by rw [cmpS_cons, if_neg h1, if_neg h2, hab])
          | gt => rw [hab] at h'; exact Ordering.noConfusion h'
          | eq =>
            rw [hab] at h'
            have hb : a = b := toL_inj a b (cmpS_eq_imp (toL a) (toL b) hab)
            have huw : u = w := by omega
            subst hb
            subst huw
            rcases cmpS_split xs ps q h' with hl | he | ⟨x', hne, hx, hq⟩
            · refine Or.inl ?_
              rw [cmpS_cons, if_neg h1, if_neg h2, hab]
              exact hl
            · exact Or.inr (Or.inl (by rw [he]))
            · exact Or.inr (Or.inr ⟨x', hne, by rw [hx]; rfl, hq⟩)
termination_by x p _ _ => sizeL x + sizeL p
decreasing_by
  · rw [sizeL_cons, sizeL_cons]; omega

/-! ### §62.3 `B` の演算と成分列 -/

theorem toL_appB : ∀ (s r : B), toL (appB r s) = toL r ++ toL s
  | .nil, r => by rw [show appB r .nil = r from rfl, show toL (.nil : B) = [] from rfl,
      List.append_nil]
  | .nd v s a, r => by
      show toL (B.nd v (appB r s) a) = _
      rw [toL_nd, toL_appB s r, toL_nd, List.append_assoc]

theorem sizeB_appB : ∀ (s r : B), sizeB (appB r s) = sizeB r + sizeB s
  | .nil, r => by show sizeB r = sizeB r + 0; omega
  | .nd v s a, r => by
      show sizeB (appB r s) + 1 + sizeB a = sizeB r + (sizeB s + 1 + sizeB a)
      rw [sizeB_appB s r]
      omega

theorem replicate_snoc {α : Type} (x : α) : ∀ (m : Nat),
    List.replicate m x ++ [x] = List.replicate (m + 1) x
  | 0 => rfl
  | k + 1 => by
      show x :: (List.replicate k x ++ [x]) = x :: List.replicate (k + 1) x
      rw [replicate_snoc x k]

theorem toL_repNode (v : Nat) (P : B) : ∀ (k : Nat),
    toL (repNode v P k) = List.replicate (k + 1) (v, P)
  | 0 => rfl
  | j + 1 => by
      show toL (B.nd v (repNode v P j) P) = _
      rw [toL_nd, toL_repNode v P j, replicate_snoc]

theorem sizeL_replicate (v : Nat) (P : B) : ∀ (m : Nat),
    sizeL (List.replicate m (v, P)) = m * (sizeB P + 1)
  | 0 => by show 0 = 0 * (sizeB P + 1); rw [Nat.zero_mul]
  | k + 1 => by
      show sizeB P + 1 + sizeL (List.replicate k (v, P)) = _
      rw [sizeL_replicate v P k, Nat.succ_mul]
      omega

/-! ### §62.4 `vArgs`: `visOK` が見る節の引数の並び -/

/-- 段 `v` の節の引数を、段が `v` 未満の節で打ち切りつつ集める。 -/
def vArgs (v : Nat) : B → List B
  | .nil => []
  | .nd u r c => vArgs v r ++ (if u < v then [] else (if u == v then [c] else []) ++ vArgs v c)

theorem vArgs_nd (v u : Nat) (r c : B) :
    vArgs v (.nd u r c)
      = vArgs v r ++ (if u < v then [] else (if u == v then [c] else []) ++ vArgs v c) := rfl

/-- **`visOK` は `vArgs` の全称。** -/
theorem visOK_iff : ∀ (s : B) (v : Nat) (a : B),
    visOK v a s = true ↔ ∀ c ∈ vArgs v s, cmpS (toL c) (toL a) = .lt := by
  intro s
  induction s with
  | nil =>
    intro v a
    exact ⟨fun _ c hc => absurd hc (by intro hm; exact List.not_mem_nil hm),
      fun _ => rfl⟩
  | nd u r c ihr ihc =>
    intro v a
    constructor
    · intro h
      have h' : (visOK v a r &&
        (if u < v then true
         else (if u == v then cmpS (toL c) (toL a) == Ordering.lt else true) && visOK v a c)) = true := h
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
      intro z hz
      rw [vArgs_nd] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (ihr v a).mp h1 z hz
      · by_cases hu : u < v
        · rw [if_pos hu] at hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
        · rw [if_neg hu] at h2 hz
          obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h2
          rcases List.mem_append.mp hz with hz | hz
          · by_cases hv : (u == v) = true
            · rw [if_pos hv] at h3 hz
              rw [List.mem_singleton.mp hz]
              exact (beq_iff_eq (a := cmpS (toL c) (toL a)) (b := Ordering.lt)).mp h3
            · rw [if_neg hv] at hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
          · exact (ihc v a).mp h4 z hz
    · intro h
      show (visOK v a r &&
        (if u < v then true
         else (if u == v then cmpS (toL c) (toL a) == Ordering.lt else true) && visOK v a c)) = true
      have hr : visOK v a r = true := (ihr v a).mpr (fun z hz => h z (by
        rw [vArgs_nd]; exact List.mem_append_left _ hz))
      rw [hr, Bool.true_and]
      by_cases hu : u < v
      · rw [if_pos hu]
      · rw [if_neg hu]
        have hc' : visOK v a c = true := (ihc v a).mpr (fun z hz => h z (by
          rw [vArgs_nd, if_neg hu]
          exact List.mem_append_right _ (List.mem_append_right _ hz)))
        rw [hc', Bool.and_true]
        by_cases hv : (u == v) = true
        · rw [if_pos hv]
          have : cmpS (toL c) (toL a) = .lt := h c (by
            rw [vArgs_nd, if_neg hu, if_pos hv]
            exact List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.mpr rfl)))
          rw [this]
          rfl
        · rw [if_neg hv]

/-- `vArgs` の要素は真部分項。 -/
theorem vArgs_size : ∀ (s : B) (v : Nat) (c : B), c ∈ vArgs v s → sizeB c < sizeB s := by
  intro s
  induction s with
  | nil => intro v c hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
  | nd u r a ihr iha =>
    intro v c hc
    rw [vArgs_nd] at hc
    have hs : sizeB (B.nd u r a) = sizeB r + 1 + sizeB a := rfl
    rcases List.mem_append.mp hc with hc | hc
    · have := ihr v c hc; omega
    · by_cases hu : u < v
      · rw [if_pos hu] at hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
      · rw [if_neg hu] at hc
        rcases List.mem_append.mp hc with hc | hc
        · by_cases hv : (u == v) = true
          · rw [if_pos hv] at hc
            rw [List.mem_singleton.mp hc]
            omega
          · rw [if_neg hv] at hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
        · have := iha v c hc; omega

/-- `stdIn` は `vArgs` の要素にも伝わる。 -/
theorem stdIn_vArgs : ∀ (s : B), stdIn s = true → ∀ (v : Nat) (c : B), c ∈ vArgs v s →
    nonIncr c = true ∧ stdIn c = true := by
  intro s
  induction s with
  | nil => intro _ v c hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
  | nd u r a ihr iha =>
    intro h v c hc
    have h' : (stdIn r && nonIncr a && visOK u a a && stdIn a) = true := h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
    obtain ⟨h3, _⟩ := (Bool.and_eq_true _ _).mp h1
    obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
    rw [vArgs_nd] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ihr h5 v c hc
    · by_cases hu : u < v
      · rw [if_pos hu] at hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
      · rw [if_neg hu] at hc
        rcases List.mem_append.mp hc with hc | hc
        · by_cases hv : (u == v) = true
          · rw [if_pos hv] at hc
            rw [List.mem_singleton.mp hc]
            exact ⟨h6, h2⟩
          · rw [if_neg hv] at hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
        · exact iha h2 v c hc

/-! #### `nonIncrL` の切り出し -/

theorem nonIncrL_suffix : ∀ (p q : List (Nat × B)), nonIncrL (p ++ q) = true → nonIncrL q = true
  | [], q, h => h
  | x :: p, q, h => by
      have h' : nonIncrL (x :: (p ++ q)) = true := h
      rw [nonIncrL_cons] at h'
      exact nonIncrL_suffix p q ((Bool.and_eq_true _ _).mp h').2


/-! ### §62.5 `repB` の式と補助 -/

theorem cmpS_nil_lt : ∀ (l : List (Nat × B)), l ≠ [] → cmpS [] l = .lt
  | [], h => absurd rfl h
  | y :: ys, _ => cmpS_nil_cons y ys

theorem repB_arg_nil (v : Nat) (r : B) (n : Nat) : repB (.nd v r .nil) n = .nil := rfl
theorem repB_base (v : Nat) (r P : B) (n : Nat) :
    repB (.nd v r (.nd 0 P .nil)) n = appB r (repNode v P n) := rfl
theorem repB_rec1 (v : Nat) (r P : B) (u2 : Nat) (s2 c2 : B) (n : Nat) :
    repB (.nd v r (.nd 0 P (.nd u2 s2 c2))) n = .nd v r (repB (.nd 0 P (.nd u2 s2 c2)) n) := rfl
theorem repB_rec2 (v : Nat) (r : B) (k : Nat) (P c : B) (n : Nat) :
    repB (.nd v r (.nd (k + 1) P c)) n = .nd v r (repB (.nd (k + 1) P c) n) := rfl

theorem vArgs_appB : ∀ (X : B) (v : Nat) (r : B),
    vArgs v (appB r X) = vArgs v r ++ vArgs v X
  | .nil, v, r => by
      show vArgs v r = vArgs v r ++ []
      rw [List.append_nil]
  | .nd u X a, v, r => by
      show vArgs v (B.nd u (appB r X) a) = _
      rw [vArgs_nd, vArgs_appB X v r, vArgs_nd, List.append_assoc]

theorem mem_vArgs_repNode : ∀ (k : Nat) (v u : Nat) (P z : B), z ∈ vArgs v (repNode u P k) →
    ¬ (u < v) ∧ ((z = P ∧ (u == v) = true) ∨ z ∈ vArgs v P) := by
  intro k
  induction k with
  | zero =>
    intro v u P z hz
    have hz' : z ∈ vArgs v (B.nd u .nil P) := hz
    rw [vArgs_nd] at hz'
    rcases List.mem_append.mp hz' with h | h
    · exact absurd h (by intro hm; exact List.not_mem_nil hm)
    · by_cases hu : u < v
      · rw [if_pos hu] at h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
      · rw [if_neg hu] at h
        refine ⟨hu, ?_⟩
        rcases List.mem_append.mp h with h | h
        · by_cases hv : (u == v) = true
          · rw [if_pos hv] at h; exact Or.inl ⟨List.mem_singleton.mp h, hv⟩
          · rw [if_neg hv] at h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
        · exact Or.inr h
  | succ j ih =>
    intro v u P z hz
    have hz' : z ∈ vArgs v (B.nd u (repNode u P j) P) := hz
    rw [vArgs_nd] at hz'
    rcases List.mem_append.mp hz' with h | h
    · exact ih v u P z h
    · by_cases hu : u < v
      · rw [if_pos hu] at h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
      · rw [if_neg hu] at h
        refine ⟨hu, ?_⟩
        rcases List.mem_append.mp h with h | h
        · by_cases hv : (u == v) = true
          · rw [if_pos hv] at h; exact Or.inl ⟨List.mem_singleton.mp h, hv⟩
          · rw [if_neg hv] at h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
        · exact Or.inr h

/-- 最上位の成分の引数は `vArgs` に入る。 -/
theorem mem_toL_vArgs : ∀ (s : B) (u : Nat) (c : B), (u, c) ∈ toL s → c ∈ vArgs u s := by
  intro s
  induction s with
  | nil => intro u c h; exact absurd h (by intro hm; exact List.not_mem_nil hm)
  | nd u' r c' ihr _ =>
    intro u c h
    rw [toL_nd] at h
    rw [vArgs_nd]
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left _ (ihr u c h)
    · have he : (u', c') = (u, c) := (List.mem_singleton.mp h).symm
      injection he with h1 h2
      subst h1
      subst h2
      refine List.mem_append_right _ ?_
      rw [if_neg (show ¬ (u' < u') by omega), if_pos (show (u' == u') = true from beq_self_eq_true u')]
      exact List.mem_append_left _ (List.mem_singleton.mpr rfl)

/-- 比較の向きを入れ替える。 -/
theorem cmpS_swap : ∀ (x y : List (Nat × B)), cmpS y x = (cmpS x y).swap
  | [], [] => by rw [cmpS_nil_nil]; rfl
  | [], y :: ys => by rw [cmpS_nil_cons, cmpS_cons_nil]; rfl
  | x :: xs, [] => by rw [cmpS_nil_cons, cmpS_cons_nil]; rfl
  | (u, a) :: xs, (w, b) :: ys => by
      rw [cmpS_cons, cmpS_cons]
      by_cases h1 : u < w
      · rw [if_neg (show ¬ (w < u) by omega), if_pos h1, if_pos h1]
        rfl
      · by_cases h2 : w < u
        · rw [if_pos h2, if_neg h1, if_pos h2]
          rfl
        · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]
          rw [cmpS_swap (toL a) (toL b)]
          cases hab : cmpS (toL a) (toL b) with
          | lt => rfl
          | gt => rfl
          | eq => exact cmpS_swap xs ys
termination_by x y => sizeL x + sizeL y
decreasing_by
  · rw [sizeL_toL, sizeL_toL, sizeL_cons, sizeL_cons]; omega
  · rw [sizeL_cons, sizeL_cons]; omega

theorem cmpS_gt_lt {x y : List (Nat × B)} (h : cmpS x y = .gt) : cmpS y x = .lt := by
  rw [cmpS_swap x y, h]; rfl

theorem cmpS_lt_gt {x y : List (Nat × B)} (h : cmpS x y = .lt) : cmpS y x = .gt := by
  rw [cmpS_swap x y, h]; rfl

/-- 降べきの尻尾は同じ成分の繰り返しより短ければ小さい。 -/
theorem rep_tail : ∀ (m : Nat) (u : Nat) (P : B) (rest : List (Nat × B)),
    nonIncrL ((u, P) :: rest) = true → sizeL rest < m * (sizeB P + 1) →
    cmpS rest (List.replicate m (u, P)) = .lt := by
  intro m
  induction m with
  | zero => intro u P rest _ hs; rw [Nat.zero_mul] at hs; omega
  | succ j ih =>
    intro u P rest hni hs
    cases rest with
    | nil => exact cmpS_nil_cons (u, P) (List.replicate j (u, P))
    | cons y ys =>
      rw [nonIncrL_cons] at hni
      obtain ⟨hhd, hni2⟩ := (Bool.and_eq_true _ _).mp hni
      have hne : ¬ (cmpS [(u, P)] [(y.1, y.2)] = .lt) := by
        intro hc
        rw [show hdOK (u, P) (y :: ys) = !(cmpN (u, P).1 (u, P).2 y.1 y.2 == Ordering.lt) from rfl,
          show cmpN (u, P).1 (u, P).2 y.1 y.2 = cmpS [(u, P)] [(y.1, y.2)] from rfl, hc] at hhd
        exact Bool.noConfusion hhd
      rw [cmpS_cons] at hne
      have hu1 : ¬ (u < y.1) := by
        intro hc; rw [if_pos hc] at hne; exact hne rfl
      rw [if_neg hu1] at hne
      show cmpS ((y.1, y.2) :: ys) ((u, P) :: List.replicate j (u, P)) = .lt
      rw [cmpS_cons]
      by_cases h1 : y.1 < u
      · rw [if_pos h1]
      · rw [if_neg h1, if_neg hu1]
        rw [if_neg h1] at hne
        cases hpy : cmpS (toL P) (toL y.2) with
        | lt => rw [hpy] at hne; exact absurd rfl hne
        | gt => rw [cmpS_gt_lt hpy]
        | eq =>
          have hyP : y.2 = P := toL_inj y.2 P (cmpS_eq_imp (toL y.2) (toL P)
            (by rw [cmpS_swap (toL P) (toL y.2), hpy]; rfl))
          rw [hyP, cmpS_refl]
          refine ih u P ys ?_ ?_
          · have hy : y = (u, P) := by
              have hu : y.1 = u := by omega
              rw [← hyP, ← hu]
            rw [← hy]
            exact hni2
          · have hsz : sizeL (y :: ys) = sizeB y.2 + 1 + sizeL ys := rfl
            rw [hsz, hyP, Nat.succ_mul] at hs
            omega


/-! #### `visOK` の分解 -/

theorem visOK_nd_eq (v u : Nat) (ref r c : B) :
    visOK v ref (.nd u r c)
      = (visOK v ref r &&
         (if u < v then true
          else (if u == v then cmpS (toL c) (toL ref) == Ordering.lt else true)
                 && visOK v ref c)) := rfl

theorem visOK_nd_r {v u : Nat} {ref r c : B} (h : visOK v ref (.nd u r c) = true) :
    visOK v ref r = true := by
  rw [visOK_nd_eq] at h
  exact ((Bool.and_eq_true _ _).mp h).1

theorem visOK_nd_c {v u : Nat} {ref r c : B} (hu : ¬ (u < v))
    (h : visOK v ref (.nd u r c) = true) : visOK v ref c = true := by
  rw [visOK_nd_eq, if_neg hu] at h
  exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).2).2

theorem visOK_nd_arg {v u : Nat} {ref r c : B} (hu : ¬ (u < v)) (hv : (u == v) = true)
    (h : visOK v ref (.nd u r c) = true) : cmpS (toL c) (toL ref) = .lt := by
  rw [visOK_nd_eq, if_neg hu, if_pos hv] at h
  have := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).2).1
  exact (beq_iff_eq (a := cmpS (toL c) (toL ref)) (b := Ordering.lt)).mp this

theorem visOK_nd_mk {v u : Nat} {ref r c : B} (h1 : visOK v ref r = true)
    (h2 : ¬ (u < v) → visOK v ref c = true)
    (h3 : ¬ (u < v) → (u == v) = true → cmpS (toL c) (toL ref) = .lt) :
    visOK v ref (.nd u r c) = true := by
  rw [visOK_nd_eq, h1, Bool.true_and]
  by_cases hu : u < v
  · rw [if_pos hu]
  · rw [if_neg hu, h2 hu, Bool.and_true]
    by_cases hv : (u == v) = true
    · rw [if_pos hv, h3 hu hv]; rfl
    · rw [if_neg hv]

/-! ### §62.6 `repB` は真に小さい -/

theorem repB_lt : ∀ (a : B) (n : Nat), a ≠ .nil → cmpS (toL (repB a n)) (toL a) = .lt := by
  intro a
  induction a with
  | nil => intro n h; exact absurd rfl h
  | nd v r a1 _ iha =>
    intro n _
    cases a1 with
    | nil =>
      rw [repB_arg_nil]
      exact cmpS_nil_lt _ (toL_ne_nil v r .nil)
    | nd u P c =>
      cases u with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base, toL_appB, toL_nd, toL_repNode, cmpS_append_left]
          show cmpS ((v, P) :: List.replicate n (v, P)) [(v, B.nd 0 P .nil)] = .lt
          rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
            toL_nd 0 P .nil,
            cmpS_lt_self_append (toL P) [(0, (.nil : B))] (List.cons_ne_nil _ _)]
        | nd u2 s2 c2 =>
          rw [repB_rec1, toL_nd, toL_nd, cmpS_append_left]
          show cmpS [(v, repB (B.nd 0 P (.nd u2 s2 c2)) n)] [(v, B.nd 0 P (.nd u2 s2 c2))] = .lt
          rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
            iha n (by intro hc; exact B.noConfusion hc)]
      | succ k =>
        rw [repB_rec2, toL_nd, toL_nd, cmpS_append_left]
        show cmpS [(v, repB (B.nd (k + 1) P c) n)] [(v, B.nd (k + 1) P c)] = .lt
        rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
          iha n (by intro hc; exact B.noConfusion hc)]


/-! ### §62.7 二つの移送補題 -/

/-! #### 基準は据え置き -/

theorem visOK_repB : ∀ (a : B) (n v : Nat) (ref : B),
    visOK v ref a = true → visOK v ref (repB a n) = true := by
  intro a
  induction a with
  | nil => intro n v ref _; rfl
  | nd u r a1 _ iha =>
    intro n v ref h
    have hr : visOK v ref r = true := visOK_nd_r h
    cases a1 with
    | nil => rw [repB_arg_nil]; rfl
    | nd u1 P c =>
      cases u1 with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base]
          refine (visOK_iff _ v ref).mpr ?_
          intro z hz
          rw [vArgs_appB] at hz
          rcases List.mem_append.mp hz with hz | hz
          · exact (visOK_iff r v ref).mp hr z hz
          · obtain ⟨hu, hcase⟩ := mem_vArgs_repNode n v u P z hz
            rcases hcase with ⟨hzP, huv⟩ | hz2
            · have harg : cmpS (toL (B.nd 0 P .nil)) (toL ref) = .lt := visOK_nd_arg hu huv h
              have hPlt : cmpS (toL P) (toL (B.nd 0 P .nil)) = .lt := by
                rw [toL_nd 0 P .nil]
                exact cmpS_lt_self_append (toL P) [(0, (.nil : B))] (List.cons_ne_nil _ _)
              rw [hzP]
              exact cmpS_trans (toL P) _ (toL ref) hPlt harg
            · exact (visOK_iff P v ref).mp (visOK_nd_r (visOK_nd_c hu h)) z hz2
        | nd u2 s2 c2 =>
          rw [repB_rec1]
          refine visOK_nd_mk hr (fun hu => iha n v ref (visOK_nd_c hu h)) ?_
          intro hu huv
          exact cmpS_trans _ _ _ (repB_lt _ n (by intro hc; exact B.noConfusion hc))
            (visOK_nd_arg hu huv h)
      | succ k =>
        rw [repB_rec2]
        refine visOK_nd_mk hr (fun hu => iha n v ref (visOK_nd_c hu h)) ?_
        intro hu huv
        exact cmpS_trans _ _ _ (repB_lt _ n (by intro hc; exact B.noConfusion hc))
          (visOK_nd_arg hu huv h)

/-! #### 基準も動かす -/

theorem C1_repB_base (u : Nat) (r P : B) (n : Nat) (x : B)
    (hni : nonIncr x = true)
    (hs : sizeB x < sizeB (appB r (repNode u P n)))
    (hlt : cmpS (toL x) (toL (B.nd u r (.nd 0 P .nil))) = .lt) :
    cmpS (toL x) (toL (appB r (repNode u P n))) = .lt := by
  have hA : toL (appB r (repNode u P n)) = toL r ++ List.replicate (n + 1) (u, P) := by
    rw [toL_appB, toL_repNode]
  rw [toL_nd] at hlt
  rw [hA]
  rcases cmpS_split (toL x) (toL r) [(u, (B.nd 0 P .nil))] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
  · exact cmpS_lt_append _ _ _ h1
  · rw [h2]
    exact cmpS_lt_self_append (toL r) _ (List.cons_ne_nil _ _)
  · rw [hx, cmpS_append_left]
    cases x' with
    | nil => exact absurd rfl hne
    | cons y rest =>
      obtain ⟨u0, z0⟩ := y
      rw [cmpS_cons] at hq
      by_cases h1 : u0 < u
      · show cmpS ((u0, z0) :: rest) ((u, P) :: List.replicate n (u, P)) = .lt
        rw [cmpS_cons, if_pos h1]
      · rw [if_neg h1] at hq
        by_cases h2 : u < u0
        · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
        · rw [if_neg h2] at hq
          have hu0 : u0 = u := by omega
          subst hu0
          have hz : cmpS (toL z0) (toL (B.nd 0 P .nil)) = .lt := by
            cases hzz : cmpS (toL z0) (toL (B.nd 0 P .nil)) with
            | lt => rfl
            | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
            | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
          rw [toL_nd 0 P .nil] at hz
          show cmpS ((u0, z0) :: rest) ((u0, P) :: List.replicate n (u0, P)) = .lt
          rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0)]
          rcases cmpS_lt_snoc_zero (toL z0) (toL P) hz with hlt2 | heq
          · rw [hlt2]
          · have hzP : z0 = P := toL_inj z0 P heq
            subst hzP
            rw [cmpS_refl]
            refine rep_tail n u0 z0 rest ?_ ?_
            · have h3 : nonIncrL (toL r ++ ((u0, z0) :: rest)) = true := by
                rw [← hx]; exact hni
              exact nonIncrL_suffix (toL r) _ h3
            · have e1 : sizeB x = sizeB r + (sizeB z0 + 1 + sizeL rest) := by
                rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
                rfl
              have e2 : sizeB (appB r (repNode u0 z0 n))
                  = sizeB r + (n + 1) * (sizeB z0 + 1) := by
                rw [sizeB_appB, ← sizeL_toL (repNode u0 z0 n), toL_repNode, sizeL_replicate]
              rw [e1, e2, Nat.succ_mul] at hs
              omega

theorem C1_repB_rec (u : Nat) (r a1 : B) (n : Nat) (x : B)
    (hIH : ∀ (z : B), nonIncr z = true → stdIn z = true → sizeB z < sizeB (repB a1 n) →
      cmpS (toL z) (toL a1) = .lt → cmpS (toL z) (toL (repB a1 n)) = .lt)
    (_hni : nonIncr x = true) (hst : stdIn x = true)
    (hs : sizeB x < sizeB (B.nd u r (repB a1 n)))
    (hlt : cmpS (toL x) (toL (B.nd u r a1)) = .lt) :
    cmpS (toL x) (toL (B.nd u r (repB a1 n))) = .lt := by
  rw [toL_nd] at hlt
  rw [toL_nd]
  rcases cmpS_split (toL x) (toL r) [(u, a1)] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
  · exact cmpS_lt_append _ _ _ h1
  · rw [h2]
    exact cmpS_lt_self_append (toL r) _ (List.cons_ne_nil _ _)
  · rw [hx, cmpS_append_left]
    cases x' with
    | nil => exact absurd rfl hne
    | cons y rest =>
      obtain ⟨u0, z0⟩ := y
      rw [cmpS_cons] at hq
      by_cases h1 : u0 < u
      · rw [cmpS_cons, if_pos h1]
      · rw [if_neg h1] at hq
        by_cases h2 : u < u0
        · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
        · rw [if_neg h2] at hq
          have hu0 : u0 = u := by omega
          subst hu0
          have hz : cmpS (toL z0) (toL a1) = .lt := by
            cases hzz : cmpS (toL z0) (toL a1) with
            | lt => rfl
            | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
            | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
          have hmem : (u0, z0) ∈ toL x := by
            rw [hx]
            exact List.mem_append_right _ (List.mem_cons_self ..)
          obtain ⟨hnz, hsz⟩ := stdIn_vArgs x hst u0 z0 (mem_toL_vArgs x u0 z0 hmem)
          have e1 : sizeB x = sizeB r + (sizeB z0 + 1 + sizeL rest) := by
            rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
            rfl
          have e2 : sizeB (B.nd u0 r (repB a1 n)) = sizeB r + 1 + sizeB (repB a1 n) := rfl
          rw [e1, e2] at hs
          rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0),
            hIH z0 hnz hsz (by omega) hz]

theorem C1_repB : ∀ (a : B) (n : Nat) (x : B), nonIncr x = true → stdIn x = true →
    sizeB x < sizeB (repB a n) → cmpS (toL x) (toL a) = .lt →
    cmpS (toL x) (toL (repB a n)) = .lt := by
  intro a
  induction a with
  | nil =>
    intro n x _ _ hs _
    have : sizeB (repB (.nil : B) n) = 0 := rfl
    omega
  | nd u r a1 _ iha =>
    intro n x hni hst hs hlt
    cases a1 with
    | nil =>
      rw [repB_arg_nil] at hs ⊢
      have : sizeB (.nil : B) = 0 := rfl
      omega
    | nd u1 P c =>
      cases u1 with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base] at hs ⊢
          exact C1_repB_base u r P n x hni hs hlt
        | nd u2 s2 c2 =>
          rw [repB_rec1] at hs ⊢
          exact C1_repB_rec u r _ n x (fun z h1 h2 h3 h4 => iha n z h1 h2 h3 h4) hni hst hs hlt
      | succ k =>
        rw [repB_rec2] at hs ⊢
        exact C1_repB_rec u r _ n x (fun z h1 h2 h3 h4 => iha n z h1 h2 h3 h4) hni hst hs hlt


/-! #### 降べきの張り替え -/

theorem cmpS_not_lt {x y : List (Nat × B)} (h : ¬ (cmpS x y = .lt)) :
    cmpS y x = .lt ∨ x = y := by
  cases hxy : cmpS x y with
  | lt => exact absurd hxy h
  | eq => exact Or.inr (cmpS_eq_imp x y hxy)
  | gt => exact Or.inl (cmpS_gt_lt hxy)

theorem cmpS_asymm {x y : List (Nat × B)} (h : cmpS x y = .lt) : ¬ (cmpS y x = .lt) := by
  intro hc
  rw [cmpS_lt_gt h] at hc
  exact Ordering.noConfusion hc

theorem hdOK_cons (x y : Nat × B) (l : List (Nat × B)) :
    hdOK x (y :: l) = !(cmpS [(x.1, x.2)] [(y.1, y.2)] == Ordering.lt) := rfl

theorem hdOK_of_not_lt (x y : Nat × B) (l : List (Nat × B))
    (h : ¬ (cmpS [x] [y] = .lt)) : hdOK x (y :: l) = true := by
  rw [hdOK_cons]
  cases hc : (cmpS [(x.1, x.2)] [(y.1, y.2)] == Ordering.lt) with
  | false => rfl
  | true => exact absurd ((beq_iff_eq (a := cmpS [x] [y]) (b := Ordering.lt)).mp hc) h

theorem not_lt_of_hdOK {x y : Nat × B} {l : List (Nat × B)} (h : hdOK x (y :: l) = true) :
    ¬ (cmpS [x] [y] = .lt) := by
  intro hc
  rw [hdOK_cons, show cmpS [(x.1, x.2)] [(y.1, y.2)] = cmpS [x] [y] from rfl, hc] at h
  exact Bool.noConfusion h

theorem hdOK_trans {y z : Nat × B} {q : List (Nat × B)}
    (h1 : hdOK y q = true) (h2 : ¬ (cmpS [z] [y] = .lt)) : hdOK z q = true := by
  cases q with
  | nil => rfl
  | cons w q' =>
    refine hdOK_of_not_lt z w q' ?_
    intro hzw
    have hwy : ¬ (cmpS [y] [w] = .lt) := not_lt_of_hdOK h1
    rcases cmpS_not_lt hwy with hlt | heq
    · exact h2 (cmpS_trans [z] [w] [y] hzw hlt)
    · rw [← heq] at hzw; exact h2 hzw

theorem nonIncrL_replicate (u : Nat) (P : B) : ∀ (m : Nat),
    nonIncrL (List.replicate m (u, P)) = true
  | 0 => rfl
  | k + 1 => by
      show (hdOK (u, P) (List.replicate k (u, P)) && nonIncrL (List.replicate k (u, P))) = true
      rw [nonIncrL_replicate u P k, Bool.and_true]
      cases k with
      | zero => rfl
      | succ j =>
        refine hdOK_of_not_lt (u, P) (u, P) _ ?_
        rw [cmpS_refl]
        intro hc; exact Ordering.noConfusion hc

/-- **末尾の成分を、より小さい列で置き換える。** -/
theorem nonIncrL_subst : ∀ (l : List (Nat × B)) (y : Nat × B) (q : List (Nat × B)),
    nonIncrL (l ++ [y]) = true → nonIncrL q = true → hdOK y q = true →
    nonIncrL (l ++ q) = true
  | [], y, q, _, hq, _ => hq
  | z :: l', y, q, h, hq, hy => by
      have h' : (hdOK z (l' ++ [y]) && nonIncrL (l' ++ [y])) = true := h
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
      show (hdOK z (l' ++ q) && nonIncrL (l' ++ q)) = true
      rw [nonIncrL_subst l' y q h2 hq hy, Bool.and_true]
      cases l' with
      | nil => exact hdOK_trans hy (not_lt_of_hdOK h1)
      | cons w l'' => exact h1

/-! #### `repB` は降べきを保つ -/

theorem P_lt_snoc (u : Nat) (P : B) : cmpS [(u, P)] [(u, (B.nd 0 P .nil))] = .lt := by
  rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u), toL_nd 0 P .nil,
    cmpS_lt_self_append (toL P) [(0, (.nil : B))] (List.cons_ne_nil _ _)]

theorem nonIncr_repB : ∀ (a : B) (n : Nat), nonIncr a = true → nonIncr (repB a n) = true := by
  intro a
  induction a with
  | nil => intro n h; exact h
  | nd u r a1 _ iha =>
    intro n h
    have h' : nonIncrL (toL r ++ [(u, a1)]) = true := by rw [← toL_nd]; exact h
    cases a1 with
    | nil => rw [repB_arg_nil]; rfl
    | nd u1 P c =>
      cases u1 with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base]
          show nonIncrL (toL (appB r (repNode u P n))) = true
          rw [toL_appB, toL_repNode]
          refine nonIncrL_subst (toL r) (u, (B.nd 0 P .nil)) _ h'
            (nonIncrL_replicate u P (n + 1)) ?_
          exact hdOK_of_not_lt _ (u, P) _ (cmpS_asymm (P_lt_snoc u P))
        | nd u2 s2 c2 =>
          rw [repB_rec1]
          show nonIncrL (toL (B.nd u r (repB (B.nd 0 P (.nd u2 s2 c2)) n))) = true
          rw [toL_nd]
          refine nonIncrL_subst (toL r) (u, (B.nd 0 P (.nd u2 s2 c2))) _ h' rfl ?_
          refine hdOK_of_not_lt _ (u, repB (B.nd 0 P (.nd u2 s2 c2)) n) _ (cmpS_asymm ?_)
          rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
            repB_lt _ n (by intro hc; exact B.noConfusion hc)]
      | succ k =>
        rw [repB_rec2]
        show nonIncrL (toL (B.nd u r (repB (B.nd (k + 1) P c) n))) = true
        rw [toL_nd]
        refine nonIncrL_subst (toL r) (u, (B.nd (k + 1) P c)) _ h' rfl ?_
        refine hdOK_of_not_lt _ (u, repB (B.nd (k + 1) P c) n) _ (cmpS_asymm ?_)
        rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
          repB_lt _ n (by intro hc; exact B.noConfusion hc)]


/-! #### `stdIn` の閉包 -/

theorem stdIn_nd_eq (v : Nat) (r c : B) :
    stdIn (.nd v r c) = (stdIn r && nonIncr c && visOK v c c && stdIn c) := rfl

theorem and_assoc4 (x y n v d : Bool) :
    ((((x && y) && n) && v) && d) = (x && (((y && n) && v) && d)) := by
  cases x <;> cases y <;> cases n <;> cases v <;> cases d <;> rfl

/-- **基準を `P ⊕ ψ₀(0)` から `P` に縮める。** 走査対象が `P` より大きくない限り通る。 -/
theorem visOK_shrink (v : Nat) (P s : B) (hsz : sizeB s ≤ sizeB P)
    (h : visOK v (.nd 0 P .nil) s = true) : visOK v P s = true := by
  refine (visOK_iff s v P).mpr ?_
  intro z hz
  have h1 : cmpS (toL z) (toL (B.nd 0 P .nil)) = .lt := (visOK_iff s v _).mp h z hz
  rw [toL_nd 0 P .nil] at h1
  rcases cmpS_lt_snoc_zero (toL z) (toL P) h1 with hlt | heq
  · exact hlt
  · exfalso
    have he := toL_inj z P heq
    have h2 := vArgs_size s v z hz
    rw [he] at h2
    omega

theorem stdIn_appB : ∀ (X r : B), stdIn (appB r X) = (stdIn r && stdIn X)
  | .nil, r => by
      show stdIn r = (stdIn r && true)
      rw [Bool.and_true]
  | .nd v s a, r => by
      show (stdIn (appB r s) && nonIncr a && visOK v a a && stdIn a)
        = (stdIn r && (stdIn s && nonIncr a && visOK v a a && stdIn a))
      rw [stdIn_appB s r, and_assoc4]

theorem stdIn_repNode (u : Nat) (P : B) (hP1 : nonIncr P = true) (hP2 : visOK u P P = true)
    (hP3 : stdIn P = true) : ∀ (k : Nat), stdIn (repNode u P k) = true
  | 0 => by
      show (stdIn .nil && nonIncr P && visOK u P P && stdIn P) = true
      rw [hP1, hP2, hP3]
      rfl
  | j + 1 => by
      show (stdIn (repNode u P j) && nonIncr P && visOK u P P && stdIn P) = true
      rw [stdIn_repNode u P hP1 hP2 hP3 j, hP1, hP2, hP3]
      rfl

/-- **`repB` は `visOK` の自己参照版を保つ。** `stdIn (repB a n)` を仮定に取る。 -/
theorem visOK_self_repB (a : B) (n v : Nat) (hst : stdIn (repB a n) = true)
    (h : visOK v a a = true) : visOK v (repB a n) (repB a n) = true := by
  refine (visOK_iff (repB a n) v (repB a n)).mpr ?_
  intro z hz
  have h1 : cmpS (toL z) (toL a) = .lt :=
    (visOK_iff (repB a n) v a).mp (visOK_repB a n v a h) z hz
  obtain ⟨hnz, hstz⟩ := stdIn_vArgs (repB a n) hst v z hz
  exact C1_repB a n z hnz hstz (vArgs_size (repB a n) v z hz) h1

theorem stdIn_repB : ∀ (a : B) (n : Nat), stdIn a = true → stdIn (repB a n) = true := by
  intro a
  induction a with
  | nil => intro n _; rfl
  | nd u r a1 _ iha =>
    intro n h
    rw [stdIn_nd_eq] at h
    obtain ⟨h123, h4⟩ := (Bool.and_eq_true _ _).mp h
    obtain ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h123
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
    cases a1 with
    | nil => rw [repB_arg_nil]; rfl
    | nd u1 P c =>
      cases u1 with
      | zero =>
        cases c with
        | nil =>
          rw [repB_base, stdIn_appB, h1, Bool.true_and]
          have hPni : nonIncr P = true := by
            have : nonIncrL (toL P ++ [(0, (.nil : B))]) = true := by
              rw [← toL_nd 0 P .nil]; exact h2
            exact nonIncrL_dropLast (toL P) (0, .nil) this
          have hPst : stdIn P = true := by
            rw [stdIn_nd_eq] at h4
            exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp
              ((Bool.and_eq_true _ _).mp h4).1).1).1
          have hPvis : visOK u P P = true :=
            visOK_shrink u P P (by omega) (visOK_nd_r h3)
          exact stdIn_repNode u P hPni hPvis hPst n
        | nd u2 s2 c2 =>
          rw [repB_rec1, stdIn_nd_eq, h1, Bool.true_and,
            nonIncr_repB _ n h2, Bool.true_and, iha n h4, Bool.and_true,
            visOK_self_repB _ n u (iha n h4) h3]
      | succ k =>
        rw [repB_rec2, stdIn_nd_eq, h1, Bool.true_and,
          nonIncr_repB _ n h2, Bool.true_and, iha n h4, Bool.and_true,
          visOK_self_repB _ n u (iha n h4) h3]



/-! ### §62.8 `rwB` の枝: `plugB`・`iterD`・`GG` -/

theorem plugB_nil_arg (u : Nat) (s Y : B) : plugB (.nd u s .nil) Y = appB s Y := rfl
theorem plugB_rec (u : Nat) (s : B) (u2 : Nat) (s2 c2 Y : B) :
    plugB (.nd u s (.nd u2 s2 c2)) Y = .nd u s (plugB (.nd u2 s2 c2) Y) := rfl

theorem hasLowAnc_nd (w v : Nat) (s : B) (u2 : Nat) (s2 c2 : B) :
    hasLowAnc w (.nd v s (.nd u2 s2 c2))
      = (decide (v < w) || hasLowAnc w (.nd u2 s2 c2)) := rfl

theorem lastLvl_leaf (v : Nat) (s : B) : lastLvl (.nd v s .nil) = v := rfl
theorem lastLvl_nd (v : Nat) (s : B) (u2 : Nat) (s2 c2 : B) :
    lastLvl (.nd v s (.nd u2 s2 c2)) = lastLvl (.nd u2 s2 c2) := rfl

theorem rwB_leaf (w n v : Nat) (s : B) : rwB w n (.nd v s .nil) = .nd v s .nil := rfl
theorem rwB_nd (w n v : Nat) (s : B) (u2 : Nat) (s2 c2 : B) :
    rwB w n (.nd v s (.nd u2 s2 c2))
      = (if hasLowAnc w (.nd u2 s2 c2) then .nd v s (rwB w n (.nd u2 s2 c2))
         else if v < w then appB s (iterD v (.nd u2 s2 c2) n)
         else .nd v s (.nd u2 s2 c2)) := rfl

/-- `iterD` の内側。`GG v a k` は `a` の最後の節を `k` 回入れ子に差し替えたもの。 -/
def GG (v : Nat) (a : B) : Nat → B
  | 0 => plugB a .nil
  | k + 1 => plugB a (.nd v .nil (GG v a k))

theorem iterD_GG (v : Nat) (a : B) : ∀ (k : Nat), iterD v a k = .nd v .nil (GG v a k)
  | 0 => rfl
  | j + 1 => by
      show B.nd v .nil (plugB a (iterD v a j)) = _
      rw [iterD_GG v a j]
      rfl

theorem appB_iterD (v : Nat) (s a : B) (k : Nat) :
    appB s (iterD v a k) = .nd v s (GG v a k) := by
  rw [iterD_GG]
  rfl

theorem toL_iterD (v : Nat) (a : B) (k : Nat) : toL (iterD v a k) = [(v, GG v a k)] := by
  rw [iterD_GG, toL_nd]
  rfl

/-! #### `plugB` は成分列をどう変えるか -/

theorem toL_plugB_leaf (u : Nat) (s Y : B) : toL (plugB (.nd u s .nil) Y) = toL s ++ toL Y := by
  rw [plugB_nil_arg, toL_appB]

theorem toL_plugB_rec (u : Nat) (s : B) (u2 : Nat) (s2 c2 Y : B) :
    toL (plugB (.nd u s (.nd u2 s2 c2)) Y) = toL s ++ [(u, plugB (.nd u2 s2 c2) Y)] := by
  rw [plugB_rec, toL_nd]

theorem sizeB_plugB_leaf (u : Nat) (s Y : B) : sizeB (plugB (.nd u s .nil) Y)
    = sizeB s + sizeB Y := by
  rw [plugB_nil_arg, sizeB_appB]

/-- **`plugB` は真に小さい。** 差し込む列が `ψ_{lastLvl a}(0)` より小さければよい。 -/
theorem plugB_lt : ∀ (a : B) (Y : B), a ≠ .nil →
    cmpS (toL Y) [(lastLvl a, (.nil : B))] = .lt →
    cmpS (toL (plugB a Y)) (toL a) = .lt := by
  intro a
  induction a with
  | nil => intro Y h _; exact absurd rfl h
  | nd u s a2 _ iha =>
    intro Y _ hY
    cases a2 with
    | nil =>
      rw [toL_plugB_leaf, toL_nd, cmpS_append_left]
      rw [lastLvl_leaf] at hY
      exact hY
    | nd u2 s2 c2 =>
      rw [toL_plugB_rec, toL_nd, cmpS_append_left]
      show cmpS [(u, plugB (B.nd u2 s2 c2) Y)] [(u, (B.nd u2 s2 c2))] = .lt
      rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u)]
      rw [iha Y (by intro hc; exact B.noConfusion hc) (by rw [← lastLvl_nd u s u2 s2 c2]; exact hY)]

/-! #### `visOK` の伝播 -/

/-- 走査で届いた引数の中の走査は、元の走査に含まれる。 -/
theorem visOK_of_vArgs_mem : ∀ (s : B) (v u : Nat) (ref z : B), v ≤ u →
    visOK v ref s = true → z ∈ vArgs u s → visOK v ref z = true := by
  intro s
  induction s with
  | nil => intro v u ref z _ _ hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
  | nd u0 r c ihr ihc =>
    intro v u ref z hvu h hz
    rw [vArgs_nd] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact ihr v u ref z hvu (visOK_nd_r h) hz
    · by_cases hu : u0 < u
      · rw [if_pos hu] at hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
      · have hv0 : ¬ (u0 < v) := by omega
        rw [if_neg hu] at hz
        rcases List.mem_append.mp hz with hz | hz
        · by_cases hv : (u0 == u) = true
          · rw [if_pos hv] at hz
            rw [List.mem_singleton.mp hz]
            exact visOK_nd_c hv0 h
          · rw [if_neg hv] at hz; exact absurd hz (by intro hm; exact List.not_mem_nil hm)
        · exact ihc v u ref z hvu (visOK_nd_c hv0 h) hz

/-- **`plugB` は基準を据え置いたまま `visOK` を保つ。** -/
theorem visOK_plugB : ∀ (a : B) (Y : B) (v : Nat) (ref : B),
    cmpS (toL Y) [(lastLvl a, (.nil : B))] = .lt →
    visOK v ref a = true → visOK v ref Y = true →
    visOK v ref (plugB a Y) = true := by
  intro a
  induction a with
  | nil => intro Y v ref _ _ _; rfl
  | nd u s a2 _ iha =>
    intro Y v ref hY h hYv
    cases a2 with
    | nil =>
      rw [plugB_nil_arg]
      refine (visOK_iff _ v ref).mpr ?_
      intro z hz
      rw [vArgs_appB] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (visOK_iff s v ref).mp (visOK_nd_r h) z hz
      · exact (visOK_iff Y v ref).mp hYv z hz
    | nd u2 s2 c2 =>
      rw [plugB_rec]
      have hY2 : cmpS (toL Y) [(lastLvl (B.nd u2 s2 c2), (.nil : B))] = .lt := by
        rw [← lastLvl_nd u s u2 s2 c2]; exact hY
      refine visOK_nd_mk (visOK_nd_r h)
        (fun hu => iha Y v ref hY2 (visOK_nd_c hu h) hYv) ?_
      intro hu huv
      exact cmpS_trans _ _ _
        (plugB_lt (B.nd u2 s2 c2) Y (by intro hc; exact B.noConfusion hc) hY2)
        (visOK_nd_arg hu huv h)

/-- 段が `v` より低い単一成分は `vArgs v` に何も足さない。 -/
theorem visOK_low_node (v v0 : Nat) (ref G : B) (h : v0 < v) :
    visOK v ref (.nd v0 .nil G) = true := by
  rw [visOK_nd_eq, if_pos h]
  rfl


/-! #### `plugB` への移送 -/

theorem lt_leaf_lvl {u0 : Nat} {z0 : B} {rest : List (Nat × B)} {w : Nat}
    (h : cmpS ((u0, z0) :: rest) [(w, (.nil : B))] = .lt) : u0 < w := by
  rw [cmpS_cons] at h
  by_cases h1 : u0 < w
  · exact h1
  · rw [if_neg h1] at h
    by_cases h2 : w < u0
    · rw [if_pos h2] at h; exact absurd h (by intro hc; exact Ordering.noConfusion hc)
    · rw [if_neg h2] at h
      exfalso
      cases hz : cmpS (toL z0) (toL (.nil : B)) with
      | lt => exact cmpS_nil_right_ne_lt (toL z0) hz
      | gt => rw [hz] at h; exact Ordering.noConfusion h
      | eq => rw [hz] at h; exact cmpS_nil_right_ne_lt rest h

theorem sizeL_pos : ∀ (l : List (Nat × B)), l ≠ [] → 0 < sizeL l
  | [], h => absurd rfl h
  | (u, a) :: l, _ => by rw [sizeL_cons]; omega

/-- **最内の差し替え (`Y = 0`) への移送。** 大きさの条件だけで通る。 -/
theorem C1_plugB_nil : ∀ (a : B) (x : B), sizeB x < sizeB (plugB a .nil) →
    cmpS (toL x) (toL a) = .lt → cmpS (toL x) (toL (plugB a .nil)) = .lt := by
  intro a
  induction a with
  | nil => intro x hs _; exact absurd hs (by rw [show sizeB (plugB (.nil : B) .nil) = 0 from rfl]; omega)
  | nd u s a2 _ iha =>
    intro x hs hlt
    cases a2 with
    | nil =>
      rw [plugB_nil_arg, show appB s (.nil : B) = s from rfl] at hs ⊢
      rw [toL_nd] at hlt
      rcases cmpS_split (toL x) (toL s) [(u, (.nil : B))] hlt with h1 | h2 | ⟨x', hne, hx, _⟩
      · exact h1
      · exfalso
        have : sizeB x = sizeB s := by rw [← sizeL_toL, h2, sizeL_toL]
        omega
      · exfalso
        have : sizeB x = sizeB s + sizeL x' := by
          rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
        have := sizeL_pos x' hne
        omega
    | nd u2 s2 c2 =>
      rw [plugB_rec] at hs ⊢
      rw [toL_nd] at hlt
      rw [toL_nd]
      rcases cmpS_split (toL x) (toL s) [(u, (B.nd u2 s2 c2))] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
      · exact cmpS_lt_append _ _ _ h1
      · rw [h2]; exact cmpS_lt_self_append (toL s) _ (List.cons_ne_nil _ _)
      · rw [hx, cmpS_append_left]
        cases x' with
        | nil => exact absurd rfl hne
        | cons y rest =>
          obtain ⟨u0, z0⟩ := y
          rw [cmpS_cons] at hq
          by_cases h1 : u0 < u
          · rw [cmpS_cons, if_pos h1]
          · rw [if_neg h1] at hq
            by_cases h2 : u < u0
            · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
            · rw [if_neg h2] at hq
              have hu0 : u0 = u := by omega
              subst hu0
              have hz : cmpS (toL z0) (toL (B.nd u2 s2 c2)) = .lt := by
                cases hzz : cmpS (toL z0) (toL (B.nd u2 s2 c2)) with
                | lt => rfl
                | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
                | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
              have e1 : sizeB x = sizeB s + (sizeB z0 + 1 + sizeL rest) := by
                rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
                rfl
              have e2 : sizeB (B.nd u0 s (plugB (B.nd u2 s2 c2) .nil))
                  = sizeB s + 1 + sizeB (plugB (B.nd u2 s2 c2) .nil) := rfl
              rw [e1, e2] at hs
              rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0),
                iha z0 (by omega) hz]

/-- **入れ子の差し替えへの移送。** 底では `BOT` に落とす。 -/
theorem C1_plugB_cons : ∀ (a : B) (w v' : Nat) (a0 G : B), v' + 1 = w →
    hasLowAnc w a = false → lastLvl a = w →
    (∀ z : B, nonIncr z = true → stdIn z = true →
       (∀ z' ∈ vArgs v' z, cmpS (toL z') (toL a0) = .lt) →
       cmpS (toL z) (toL a0) = .lt → sizeB z < sizeB G →
       cmpS (toL z) (toL G) = .lt) →
    ∀ (x : B), nonIncr x = true → stdIn x = true →
      (∀ z' ∈ vArgs v' x, cmpS (toL z') (toL a0) = .lt) →
      sizeB x < sizeB (plugB a (.nd v' .nil G)) → cmpS (toL x) (toL a) = .lt →
      cmpS (toL x) (toL (plugB a (.nd v' .nil G))) = .lt := by
  intro a
  induction a with
  | nil =>
    intro w v' a0 G _ _ _ _ x _ _ _ hs _
    exact absurd hs (by rw [show sizeB (plugB (.nil : B) (.nd v' .nil G)) = 0 from rfl]; omega)
  | nd u s a2 _ iha =>
    intro w v' a0 G hvw hLA hll BOT x hni hst hvis hs hlt
    cases a2 with
    | nil =>
      have huw : u = w := hll
      subst huw
      rw [plugB_nil_arg] at hs ⊢
      rw [toL_nd] at hlt
      rw [toL_appB, show toL (B.nd v' (.nil : B) G) = [(v', G)] from rfl]
      rcases cmpS_split (toL x) (toL s) [(u, (.nil : B))] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
      · exact cmpS_lt_append _ _ _ h1
      · rw [h2]; exact cmpS_lt_self_append (toL s) _ (List.cons_ne_nil _ _)
      · rw [hx, cmpS_append_left]
        cases x' with
        | nil => exact absurd rfl hne
        | cons y rest =>
          obtain ⟨u0, z0⟩ := y
          have hu0 : u0 < u := lt_leaf_lvl hq
          rw [cmpS_cons]
          by_cases h1 : u0 < v'
          · rw [if_pos h1]
          · rw [if_neg h1, if_neg (show ¬ (v' < u0) by omega)]
            have hmem : (u0, z0) ∈ toL x := by
              rw [hx]; exact List.mem_append_right _ (List.mem_cons_self ..)
            have hmv : z0 ∈ vArgs u0 x := mem_toL_vArgs x u0 z0 hmem
            obtain ⟨hnz, hsz⟩ := stdIn_vArgs x hst u0 z0 hmv
            have hvisx : visOK v' a0 x = true := (visOK_iff x v' a0).mpr hvis
            have hmv' : z0 ∈ vArgs v' x := by
              have : u0 = v' := by omega
              rw [← this]; exact hmv
            have hz0a0 : cmpS (toL z0) (toL a0) = .lt := hvis z0 hmv'
            have hvz0 : ∀ z' ∈ vArgs v' z0, cmpS (toL z') (toL a0) = .lt :=
              (visOK_iff z0 v' a0).mp
                (visOK_of_vArgs_mem x v' u0 a0 z0 (by omega) hvisx hmv)
            have e1 : sizeB x = sizeB s + (sizeB z0 + 1 + sizeL rest) := by
              rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
              rfl
            have e2 : sizeB (appB s (B.nd v' (.nil : B) G)) = sizeB s + (0 + 1 + sizeB G) := by
              rw [sizeB_appB]
              rfl
            rw [e1, e2] at hs
            rw [BOT z0 hnz hsz hvz0 hz0a0 (by omega)]
    | nd u2 s2 c2 =>
      have hLA2 : hasLowAnc w (B.nd u2 s2 c2) = false := by
        rw [hasLowAnc_nd] at hLA
        cases hd : hasLowAnc w (B.nd u2 s2 c2) with
        | false => rfl
        | true => rw [hd, Bool.or_true] at hLA; exact absurd hLA (by intro hc; exact Bool.noConfusion hc)
      have huw : ¬ (u < w) := by
        rw [hasLowAnc_nd] at hLA
        intro hc
        rw [show decide (u < w) = true from decide_eq_true hc, Bool.true_or] at hLA
        exact Bool.noConfusion hLA
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd u s u2 s2 c2]; exact hll
      rw [plugB_rec] at hs ⊢
      rw [toL_nd] at hlt
      rw [toL_nd]
      rcases cmpS_split (toL x) (toL s) [(u, (B.nd u2 s2 c2))] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
      · exact cmpS_lt_append _ _ _ h1
      · rw [h2]; exact cmpS_lt_self_append (toL s) _ (List.cons_ne_nil _ _)
      · rw [hx, cmpS_append_left]
        cases x' with
        | nil => exact absurd rfl hne
        | cons y rest =>
          obtain ⟨u0, z0⟩ := y
          rw [cmpS_cons] at hq
          by_cases h1 : u0 < u
          · rw [cmpS_cons, if_pos h1]
          · rw [if_neg h1] at hq
            by_cases h2 : u < u0
            · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
            · rw [if_neg h2] at hq
              have hu0 : u0 = u := by omega
              subst hu0
              have hz : cmpS (toL z0) (toL (B.nd u2 s2 c2)) = .lt := by
                cases hzz : cmpS (toL z0) (toL (B.nd u2 s2 c2)) with
                | lt => rfl
                | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
                | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
              have hmem : (u0, z0) ∈ toL x := by
                rw [hx]; exact List.mem_append_right _ (List.mem_cons_self ..)
              have hmv : z0 ∈ vArgs u0 x := mem_toL_vArgs x u0 z0 hmem
              obtain ⟨hnz, hsz⟩ := stdIn_vArgs x hst u0 z0 hmv
              have hvisx : visOK v' a0 x = true := (visOK_iff x v' a0).mpr hvis
              have hvz0 : ∀ z' ∈ vArgs v' z0, cmpS (toL z') (toL a0) = .lt :=
                (visOK_iff z0 v' a0).mp
                  (visOK_of_vArgs_mem x v' u0 a0 z0 (by omega) hvisx hmv)
              have e1 : sizeB x = sizeB s + (sizeB z0 + 1 + sizeL rest) := by
                rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
                rfl
              have e2 : sizeB (B.nd u0 s (plugB (B.nd u2 s2 c2) (.nd v' .nil G)))
                  = sizeB s + 1 + sizeB (plugB (B.nd u2 s2 c2) (.nd v' .nil G)) := rfl
              rw [e1, e2] at hs
              rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0),
                iha w v' a0 G hvw hLA2 hll2 BOT z0 hnz hsz hvz0 (by omega) hz]

/-- **`GG` への移送。** 入れ子の深さ `k` の帰納。 -/
theorem C1_GG : ∀ (k : Nat) (a0 : B) (w v' : Nat), v' + 1 = w →
    hasLowAnc w a0 = false → lastLvl a0 = w →
    ∀ (x : B), nonIncr x = true → stdIn x = true →
      (∀ z' ∈ vArgs v' x, cmpS (toL z') (toL a0) = .lt) →
      sizeB x < sizeB (GG v' a0 k) → cmpS (toL x) (toL a0) = .lt →
      cmpS (toL x) (toL (GG v' a0 k)) = .lt := by
  intro k
  induction k with
  | zero =>
    intro a0 w v' _ _ _ x _ _ _ hs hlt
    exact C1_plugB_nil a0 x hs hlt
  | succ j ih =>
    intro a0 w v' hvw hLA hll x hni hst hvis hs hlt
    exact C1_plugB_cons a0 w v' a0 (GG v' a0 j) hvw hLA hll
      (fun z h1 h2 h3 h4 h5 => ih a0 w v' hvw hLA hll z h1 h2 h3 h5 h4)
      x hni hst hvis hs hlt


/-! #### `GG` の基本性質 -/

theorem GG_lt (v' : Nat) (a0 : B) (hne : a0 ≠ .nil) (hv : v' < lastLvl a0) :
    ∀ (k : Nat), cmpS (toL (GG v' a0 k)) (toL a0) = .lt
  | 0 => plugB_lt a0 .nil hne (cmpS_nil_cons _ _)
  | j + 1 => by
      show cmpS (toL (plugB a0 (.nd v' .nil (GG v' a0 j)))) (toL a0) = .lt
      refine plugB_lt a0 _ hne ?_
      rw [show toL (B.nd v' (.nil : B) (GG v' a0 j)) = [(v', GG v' a0 j)] from rfl,
        cmpS_cons, if_pos hv]

theorem visOK_Z (v v' : Nat) (ref G : B)
    (hG : (v' == v) = true → cmpS (toL G) (toL ref) = .lt)
    (hGv : ¬ (v' < v) → visOK v ref G = true) : visOK v ref (.nd v' .nil G) = true :=
  visOK_nd_mk rfl hGv (fun _ huv => hG huv)

theorem visOK_GG (v v' : Nat) (a0 ref : B) (hne : a0 ≠ .nil) (hv : v' < lastLvl a0)
    (h0 : visOK v ref a0 = true)
    (hGref : (v' == v) = true → ∀ j, cmpS (toL (GG v' a0 j)) (toL ref) = .lt) :
    ∀ (k : Nat), visOK v ref (GG v' a0 k) = true
  | 0 => by
      show visOK v ref (plugB a0 .nil) = true
      exact visOK_plugB a0 .nil v ref (cmpS_nil_cons _ _) h0 rfl
  | j + 1 => by
      show visOK v ref (plugB a0 (.nd v' .nil (GG v' a0 j))) = true
      refine visOK_plugB a0 _ v ref ?_ h0 ?_
      · rw [show toL (B.nd v' (.nil : B) (GG v' a0 j)) = [(v', GG v' a0 j)] from rfl,
          cmpS_cons, if_pos hv]
      · exact visOK_Z v v' ref _ (fun huv => hGref huv j)
          (fun _ => visOK_GG v v' a0 ref hne hv h0 hGref j)

/-! #### `plugB` は降べきを保つ -/

theorem nonIncr_plugB : ∀ (a Y : B), a ≠ .nil → nonIncr a = true →
    nonIncrL (toL Y) = true → hdOK (lastLvl a, (.nil : B)) (toL Y) = true →
    cmpS (toL Y) [(lastLvl a, (.nil : B))] = .lt →
    nonIncr (plugB a Y) = true := by
  intro a
  induction a with
  | nil => intro Y h _ _ _ _; exact absurd rfl h
  | nd u s a2 _ iha =>
    intro Y _ hni hYni hYhd hYlt
    cases a2 with
    | nil =>
      show nonIncrL (toL (plugB (B.nd u s .nil) Y)) = true
      rw [toL_plugB_leaf]
      refine nonIncrL_subst (toL s) (u, (.nil : B)) (toL Y) ?_ hYni hYhd
      rw [← toL_nd]
      exact hni
    | nd u2 s2 c2 =>
      show nonIncrL (toL (plugB (B.nd u s (.nd u2 s2 c2)) Y)) = true
      rw [toL_plugB_rec]
      refine nonIncrL_subst (toL s) (u, (B.nd u2 s2 c2)) _ (by rw [← toL_nd]; exact hni) rfl ?_
      refine hdOK_of_not_lt _ (u, plugB (B.nd u2 s2 c2) Y) _ (cmpS_asymm ?_)
      rw [cmpS_cons, if_neg (Nat.lt_irrefl u), if_neg (Nat.lt_irrefl u),
        plugB_lt (B.nd u2 s2 c2) Y (by intro hc; exact B.noConfusion hc)
          (by rw [← lastLvl_nd u s u2 s2 c2]; exact hYlt)]

theorem nonIncr_GG (v' : Nat) (a0 : B) (hne : a0 ≠ .nil) (hv : v' < lastLvl a0)
    (hni : nonIncr a0 = true) : ∀ (k : Nat), nonIncr (GG v' a0 k) = true
  | 0 => by
      show nonIncr (plugB a0 .nil) = true
      exact nonIncr_plugB a0 .nil hne hni rfl rfl (cmpS_nil_cons _ _)
  | j + 1 => by
      show nonIncr (plugB a0 (.nd v' .nil (GG v' a0 j))) = true
      have hlt : cmpS (toL (B.nd v' (.nil : B) (GG v' a0 j))) [(lastLvl a0, (.nil : B))] = .lt := by
        rw [show toL (B.nd v' (.nil : B) (GG v' a0 j)) = [(v', GG v' a0 j)] from rfl,
          cmpS_cons, if_pos hv]
      refine nonIncr_plugB a0 _ hne hni rfl ?_ hlt
      exact hdOK_of_not_lt _ (v', GG v' a0 j) _ (cmpS_asymm hlt)


/-! #### `stdIn` と `plugB` -/

theorem hdOK_leaf (w : Nat) (Y : B) (h : cmpS (toL Y) [(w, (.nil : B))] = .lt) :
    hdOK (w, (.nil : B)) (toL Y) = true := by
  cases hY : toL Y with
  | nil => rfl
  | cons y ys =>
    rw [hY] at h
    obtain ⟨u0, z0⟩ := y
    have hu0 : u0 < w := lt_leaf_lvl h
    refine hdOK_of_not_lt _ (u0, z0) _ ?_
    rw [cmpS_cons, if_neg (show ¬ (w < u0) by omega), if_pos hu0]
    intro hc; exact Ordering.noConfusion hc

theorem stdIn_plugB : ∀ (a : B) (w v' : Nat) (a0 Y : B), v' + 1 = w →
    hasLowAnc w a = false → lastLvl a = w →
    cmpS (toL Y) [(w, (.nil : B))] = .lt →
    nonIncrL (toL Y) = true → stdIn Y = true →
    (∀ (u : Nat) (ref : B), w ≤ u → visOK u ref Y = true) →
    visOK v' a0 Y = true →
    visOK v' a0 a = true →
    stdIn a = true →
    (∀ (a' : B), hasLowAnc w a' = false → lastLvl a' = w →
      ∀ x : B, nonIncr x = true → stdIn x = true →
        (∀ z' ∈ vArgs v' x, cmpS (toL z') (toL a0) = .lt) →
        sizeB x < sizeB (plugB a' Y) → cmpS (toL x) (toL a') = .lt →
        cmpS (toL x) (toL (plugB a' Y)) = .lt) →
    stdIn (plugB a Y) = true := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; rfl
  | nd u s a2 _ iha =>
    intro w v' a0 Y hvw hLA hll hYlt hYni hYst hYvis hYv' hva hst hTR
    have hst4 : (stdIn s && nonIncr a2 && visOK u a2 a2 && stdIn a2) = true := hst
    obtain ⟨hst123, hsta2⟩ := (Bool.and_eq_true _ _).mp hst4
    obtain ⟨hst12, hvisa2⟩ := (Bool.and_eq_true _ _).mp hst123
    obtain ⟨hsts, hnia2⟩ := (Bool.and_eq_true _ _).mp hst12
    cases a2 with
    | nil =>
      rw [plugB_nil_arg, stdIn_appB, hsts, hYst]
      rfl
    | nd u2 s2 c2 =>
      have hLA2 : hasLowAnc w (B.nd u2 s2 c2) = false := by
        rw [hasLowAnc_nd] at hLA
        cases hd : hasLowAnc w (B.nd u2 s2 c2) with
        | false => rfl
        | true =>
          rw [hd, Bool.or_true] at hLA
          exact absurd hLA (by intro hc; exact Bool.noConfusion hc)
      have huw : ¬ (u < w) := by
        rw [hasLowAnc_nd] at hLA
        intro hc
        rw [show decide (u < w) = true from decide_eq_true hc, Bool.true_or] at hLA
        exact Bool.noConfusion hLA
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd u s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      have hYlt2 : cmpS (toL Y) [(lastLvl (B.nd u2 s2 c2), (.nil : B))] = .lt := by
        rw [hll2]; exact hYlt
      have hva2 : visOK v' a0 (B.nd u2 s2 c2) := visOK_nd_c (show ¬ (u < v') by omega) hva
      have hIH : stdIn (plugB (B.nd u2 s2 c2) Y) = true :=
        iha w v' a0 Y hvw hLA2 hll2 hYlt hYni hYst hYvis hYv' hva2 hsta2 hTR
      have hnip : nonIncr (plugB (B.nd u2 s2 c2) Y) = true :=
        nonIncr_plugB _ Y hne2 hnia2 hYni (by rw [hll2]; exact hdOK_leaf w Y hYlt) hYlt2
      have hvp : visOK v' a0 (plugB (B.nd u2 s2 c2) Y) = true :=
        visOK_plugB _ Y v' a0 hYlt2 hva2 hYv'
      have hself : visOK u (plugB (B.nd u2 s2 c2) Y) (plugB (B.nd u2 s2 c2) Y) = true := by
        have h1 : visOK u (B.nd u2 s2 c2) (plugB (B.nd u2 s2 c2) Y) = true :=
          visOK_plugB _ Y u _ hYlt2 hvisa2 (hYvis u _ (by omega))
        refine (visOK_iff _ u _).mpr ?_
        intro z hz
        have hz1 : cmpS (toL z) (toL (B.nd u2 s2 c2)) = .lt :=
          (visOK_iff _ u _).mp h1 z hz
        obtain ⟨hnz, hstz⟩ := stdIn_vArgs _ hIH u z hz
        have hvz : ∀ z' ∈ vArgs v' z, cmpS (toL z') (toL a0) = .lt :=
          (visOK_iff z v' a0).mp
            (visOK_of_vArgs_mem _ v' u a0 z (by omega) hvp hz)
        exact hTR (B.nd u2 s2 c2) hLA2 hll2 z hnz hstz hvz (vArgs_size _ u z hz) hz1
      rw [plugB_rec, stdIn_nd_eq, hsts, hnip, hself, hIH]
      rfl


/-! #### `GG` の `stdIn` と自己 `visOK` -/

theorem visOK_self_GG (v' : Nat) (a0 : B) (w : Nat) (hvw : v' + 1 = w)
    (hne : a0 ≠ .nil) (hLA : hasLowAnc w a0 = false) (hll : lastLvl a0 = w)
    (hv0 : visOK v' a0 a0 = true) (k : Nat) (hst : stdIn (GG v' a0 k) = true) :
    visOK v' (GG v' a0 k) (GG v' a0 k) = true := by
  have hv : v' < lastLvl a0 := by rw [hll]; omega
  have h1 : visOK v' a0 (GG v' a0 k) = true :=
    visOK_GG v' v' a0 a0 hne hv hv0 (fun _ j => GG_lt v' a0 hne hv j) k
  refine (visOK_iff _ v' _).mpr ?_
  intro z hz
  have hz1 : cmpS (toL z) (toL a0) = .lt := (visOK_iff _ v' a0).mp h1 z hz
  obtain ⟨hnz, hstz⟩ := stdIn_vArgs _ hst v' z hz
  have hvz : ∀ z' ∈ vArgs v' z, cmpS (toL z') (toL a0) = .lt :=
    (visOK_iff z v' a0).mp (visOK_of_vArgs_mem _ v' v' a0 z (Nat.le_refl v') h1 hz)
  exact C1_GG k a0 w v' hvw hLA hll z hnz hstz hvz (vArgs_size _ v' z hz) hz1

theorem stdIn_GG (v' : Nat) (a0 : B) (w : Nat) (hvw : v' + 1 = w)
    (hne : a0 ≠ .nil) (hLA : hasLowAnc w a0 = false) (hll : lastLvl a0 = w)
    (hni0 : nonIncr a0 = true) (hst0 : stdIn a0 = true) (hv0 : visOK v' a0 a0 = true) :
    ∀ (k : Nat), stdIn (GG v' a0 k) = true
  | 0 => by
      show stdIn (plugB a0 .nil) = true
      exact stdIn_plugB a0 w v' a0 .nil hvw hLA hll (cmpS_nil_cons _ _) rfl rfl
        (fun _ _ _ => rfl) rfl hv0 hst0
        (fun a' _ _ x _ _ _ hs hlt => C1_plugB_nil a' x hs hlt)
  | j + 1 => by
      have hv : v' < lastLvl a0 := by rw [hll]; omega
      have hstj : stdIn (GG v' a0 j) = true :=
        stdIn_GG v' a0 w hvw hne hLA hll hni0 hst0 hv0 j
      have hYlt : cmpS (toL (B.nd v' (.nil : B) (GG v' a0 j))) [(w, (.nil : B))] = .lt := by
        rw [show toL (B.nd v' (.nil : B) (GG v' a0 j)) = [(v', GG v' a0 j)] from rfl,
          cmpS_cons, if_pos (show v' < w by omega)]
      have hYst : stdIn (B.nd v' (.nil : B) (GG v' a0 j)) = true := by
        rw [stdIn_nd_eq, nonIncr_GG v' a0 hne hv hni0 j,
          visOK_self_GG v' a0 w hvw hne hLA hll hv0 j hstj, hstj]
        rfl
      show stdIn (plugB a0 (.nd v' .nil (GG v' a0 j))) = true
      refine stdIn_plugB a0 w v' a0 _ hvw hLA hll hYlt rfl hYst
        (fun u ref hu => visOK_low_node u v' ref _ (by omega)) ?_ hv0 hst0 ?_
      · exact visOK_Z v' v' a0 _ (fun _ => GG_lt v' a0 hne hv j)
          (fun _ => visOK_GG v' v' a0 a0 hne hv hv0 (fun _ i => GG_lt v' a0 hne hv i) j)
      · exact fun a' hLA' hll' x hnx hsx hvx hs hlt =>
          C1_plugB_cons a' w v' a0 (GG v' a0 j) hvw hLA' hll'
            (fun z h1 h2 h3 h4 h5 => C1_GG j a0 w v' hvw hLA hll z h1 h2 h3 h5 h4)
            x hnx hsx hvx hs hlt


/-! ### §62.9 `rwB` の枝: 組み立て -/

theorem stdIn_toL_visOK : ∀ (s : B), stdIn s = true → ∀ (u : Nat) (c : B),
    (u, c) ∈ toL s → visOK u c c = true := by
  intro s
  induction s with
  | nil => intro _ u c hc; exact absurd hc (by intro hm; exact List.not_mem_nil hm)
  | nd u0 r c0 ihr _ =>
    intro h u c hc
    have h4 : (stdIn r && nonIncr c0 && visOK u0 c0 c0 && stdIn c0) = true := h
    obtain ⟨h123, _⟩ := (Bool.and_eq_true _ _).mp h4
    obtain ⟨h12, hv⟩ := (Bool.and_eq_true _ _).mp h123
    obtain ⟨hr, _⟩ := (Bool.and_eq_true _ _).mp h12
    rw [toL_nd] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ihr hr u c hc
    · have he : (u0, c0) = (u, c) := (List.mem_singleton.mp hc).symm
      injection he with h1 h2
      rw [← h1, ← h2]
      exact hv

/-- 最後の成分の引数だけを差し替える移送 (`repB` でも `rwB` でも同じ形)。 -/
theorem C1_rec_gen (u : Nat) (r a1 g : B) (x : B)
    (hIH : ∀ (z : B), nonIncr z = true → stdIn z = true → visOK u z z = true →
      sizeB z < sizeB g → cmpS (toL z) (toL a1) = .lt → cmpS (toL z) (toL g) = .lt)
    (hst : stdIn x = true)
    (hs : sizeB x < sizeB (B.nd u r g))
    (hlt : cmpS (toL x) (toL (B.nd u r a1)) = .lt) :
    cmpS (toL x) (toL (B.nd u r g)) = .lt := by
  rw [toL_nd] at hlt
  rw [toL_nd]
  rcases cmpS_split (toL x) (toL r) [(u, a1)] hlt with h1 | h2 | ⟨x', hne, hx, hq⟩
  · exact cmpS_lt_append _ _ _ h1
  · rw [h2]
    exact cmpS_lt_self_append (toL r) _ (List.cons_ne_nil _ _)
  · rw [hx, cmpS_append_left]
    cases x' with
    | nil => exact absurd rfl hne
    | cons y rest =>
      obtain ⟨u0, z0⟩ := y
      rw [cmpS_cons] at hq
      by_cases h1 : u0 < u
      · rw [cmpS_cons, if_pos h1]
      · rw [if_neg h1] at hq
        by_cases h2 : u < u0
        · rw [if_pos h2] at hq; exact Ordering.noConfusion hq
        · rw [if_neg h2] at hq
          have hu0 : u0 = u := by omega
          subst hu0
          have hz : cmpS (toL z0) (toL a1) = .lt := by
            cases hzz : cmpS (toL z0) (toL a1) with
            | lt => rfl
            | gt => rw [hzz] at hq; exact Ordering.noConfusion hq
            | eq => rw [hzz] at hq; exact absurd hq (cmpS_nil_right_ne_lt rest)
          have hmem : (u0, z0) ∈ toL x := by
            rw [hx]
            exact List.mem_append_right _ (List.mem_cons_self ..)
          obtain ⟨hnz, hsz⟩ := stdIn_vArgs x hst u0 z0 (mem_toL_vArgs x u0 z0 hmem)
          have hvz : visOK u0 z0 z0 = true := stdIn_toL_visOK x hst u0 z0 hmem
          have e1 : sizeB x = sizeB r + (sizeB z0 + 1 + sizeL rest) := by
            rw [← sizeL_toL, hx, sizeL_append, sizeL_toL]
            rfl
          have e2 : sizeB (B.nd u0 r g) = sizeB r + 1 + sizeB g := rfl
          rw [e1, e2] at hs
          rw [cmpS_cons, if_neg (Nat.lt_irrefl u0), if_neg (Nat.lt_irrefl u0),
            hIH z0 hnz hsz hvz (by omega) hz]

/-- 最も近い低い祖先の段は `w - 1` ちょうど。`nfLe` が効く唯一の場所。 -/
theorem lowAnc_lvl (w : Nat) : ∀ (a : B) (m : Nat), a ≠ .nil → hasLowAnc w a = false →
    lastLvl a = w → nfLe m a = true → w ≤ m := by
  intro a m hne hLA hll hnf
  cases a with
  | nil => exact absurd rfl hne
  | nd u s a2 =>
    obtain ⟨h1, _, _⟩ := (nfLe_nd_iff m u s a2).mp hnf
    cases a2 with
    | nil => rw [← hll]; exact h1
    | nd u2 s2 c2 =>
      rw [hasLowAnc_nd] at hLA
      have huw : ¬ (u < w) := by
        intro hc
        rw [show decide (u < w) = true from decide_eq_true hc, Bool.true_or] at hLA
        exact Bool.noConfusion hLA
      omega

/-- `rwB` は小さくするか、何もしない。 -/
theorem rwB_le : ∀ (a : B) (w n : Nat), lastLvl a = w →
    cmpS (toL (rwB w n a)) (toL a) = .lt ∨ rwB w n a = a := by
  intro a
  induction a with
  | nil => intro w n _; exact Or.inr rfl
  | nd v s a1 _ iha =>
    intro w n hll
    cases a1 with
    | nil => exact Or.inr rfl
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v s u2 s2 c2]; exact hll
      rw [rwB_nd]
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1]
        rcases iha w n hll2 with hlt | heq
        · refine Or.inl ?_
          rw [toL_nd, toL_nd, cmpS_append_left, cmpS_cons,
            if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v), hlt]
        · exact Or.inr (by rw [heq])
      · rw [if_neg h1]
        by_cases h2 : v < w
        · rw [if_pos h2, appB_iterD]
          refine Or.inl ?_
          rw [toL_nd, toL_nd, cmpS_append_left, cmpS_cons,
            if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
            GG_lt v (B.nd u2 s2 c2) (by intro hc; exact B.noConfusion hc)
              (by rw [hll2]; exact h2) n]
        · rw [if_neg h2]; exact Or.inr rfl

theorem nonIncr_rwB : ∀ (a : B) (w n : Nat), lastLvl a = w → nonIncr a = true →
    nonIncr (rwB w n a) = true := by
  intro a
  induction a with
  | nil => intro _ _ _ h; exact h
  | nd v s a1 _ _ =>
    intro w n hll hni
    have hni' : nonIncrL (toL s ++ [(v, a1)]) = true := by rw [← toL_nd]; exact hni
    cases a1 with
    | nil => exact hni
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [rwB_nd]
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1]
        show nonIncrL (toL (B.nd v s (rwB w n (B.nd u2 s2 c2)))) = true
        rw [toL_nd]
        refine nonIncrL_subst (toL s) (v, (B.nd u2 s2 c2)) _ hni' rfl ?_
        refine hdOK_of_not_lt _ (v, rwB w n (B.nd u2 s2 c2)) _ ?_
        rcases rwB_le (B.nd u2 s2 c2) w n hll2 with hlt | heq
        · refine cmpS_asymm ?_
          rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v), hlt]
        · rw [heq, cmpS_refl]
          intro hc; exact Ordering.noConfusion hc
      · rw [if_neg h1]
        by_cases h2 : v < w
        · rw [if_pos h2, appB_iterD]
          show nonIncrL (toL (B.nd v s (GG v (B.nd u2 s2 c2) n))) = true
          rw [toL_nd]
          refine nonIncrL_subst (toL s) (v, (B.nd u2 s2 c2)) _ hni' rfl ?_
          refine hdOK_of_not_lt _ (v, GG v (B.nd u2 s2 c2) n) _ (cmpS_asymm ?_)
          rw [cmpS_cons, if_neg (Nat.lt_irrefl v), if_neg (Nat.lt_irrefl v),
            GG_lt v (B.nd u2 s2 c2) hne2 (by rw [hll2]; exact h2) n]
        · rw [if_neg h2]; exact hni

theorem visOK_rwB : ∀ (a : B) (w n v : Nat) (ref : B), lastLvl a = w →
    visOK v ref a = true → visOK v ref (rwB w n a) = true := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ h; exact h
  | nd v0 s a1 _ iha =>
    intro w n v ref hll h
    cases a1 with
    | nil => exact h
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v0 s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [rwB_nd]
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1]
        refine visOK_nd_mk (visOK_nd_r h) (fun hu => iha w n v ref hll2 (visOK_nd_c hu h)) ?_
        intro hu huv
        rcases rwB_le (B.nd u2 s2 c2) w n hll2 with hlt | heq
        · exact cmpS_trans _ _ _ hlt (visOK_nd_arg hu huv h)
        · rw [heq]; exact visOK_nd_arg hu huv h
      · rw [if_neg h1]
        by_cases h2 : v0 < w
        · rw [if_pos h2, appB_iterD]
          have hv : v0 < lastLvl (B.nd u2 s2 c2) := by rw [hll2]; exact h2
          refine visOK_nd_mk (visOK_nd_r h) ?_ ?_
          · intro hu
            refine visOK_GG v v0 (B.nd u2 s2 c2) ref hne2 hv (visOK_nd_c hu h) ?_ n
            intro huv j
            exact cmpS_trans _ _ _ (GG_lt v0 _ hne2 hv j) (visOK_nd_arg hu huv h)
          · intro hu huv
            exact cmpS_trans _ _ _ (GG_lt v0 _ hne2 hv n) (visOK_nd_arg hu huv h)
        · rw [if_neg h2]; exact h

theorem C1_rwB : ∀ (a : B) (w n m : Nat), lastLvl a = w → nfLe m a = true →
    ∀ (x : B), nonIncr x = true → stdIn x = true →
      sizeB x < sizeB (rwB w n a) → cmpS (toL x) (toL a) = .lt →
      cmpS (toL x) (toL (rwB w n a)) = .lt := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ x _ _ _ hlt; exact hlt
  | nd v0 s a1 _ iha =>
    intro w n m hll hnf x hni hst hs hlt
    obtain ⟨_, _, hnf1⟩ := (nfLe_nd_iff m v0 s a1).mp hnf
    cases a1 with
    | nil => exact hlt
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v0 s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [rwB_nd] at hs ⊢
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1] at hs ⊢
        exact C1_rec_gen v0 s (B.nd u2 s2 c2) (rwB w n (B.nd u2 s2 c2)) x
          (fun z hz1 hz2 _ hz3 hz4 => iha w n (v0 + 1) hll2 hnf1 z hz1 hz2 hz3 hz4)
          hst hs hlt
      · rw [if_neg h1] at hs ⊢
        have hLA2 : hasLowAnc w (B.nd u2 s2 c2) = false := by
          cases hd : hasLowAnc w (B.nd u2 s2 c2) with
          | false => rfl
          | true => exact absurd hd h1
        by_cases h2 : v0 < w
        · rw [if_pos h2, appB_iterD] at hs ⊢
          have hvw : v0 + 1 = w := by
            have := lowAnc_lvl w (B.nd u2 s2 c2) (v0 + 1) hne2 hLA2 hll2 hnf1
            omega
          refine C1_rec_gen v0 s (B.nd u2 s2 c2) (GG v0 (B.nd u2 s2 c2) n) x ?_ hst hs hlt
          intro z hz1 hz2 hzv hz3 hz4
          refine C1_GG n (B.nd u2 s2 c2) w v0 hvw hLA2 hll2 z hz1 hz2 ?_ hz3 hz4
          intro z' hz'
          exact cmpS_trans _ _ _ ((visOK_iff z v0 z).mp hzv z' hz') hz4
        · rw [if_neg h2] at hs ⊢; exact hlt

theorem visOK_self_rwB (a : B) (w n m v : Nat) (hll : lastLvl a = w) (hnf : nfLe m a = true)
    (hst : stdIn (rwB w n a) = true) (h : visOK v a a = true) :
    visOK v (rwB w n a) (rwB w n a) = true := by
  refine (visOK_iff _ v _).mpr ?_
  intro z hz
  have h1 : cmpS (toL z) (toL a) = .lt :=
    (visOK_iff _ v a).mp (visOK_rwB a w n v a hll h) z hz
  obtain ⟨hnz, hstz⟩ := stdIn_vArgs _ hst v z hz
  exact C1_rwB a w n m hll hnf z hnz hstz (vArgs_size _ v z hz) h1

theorem stdIn_rwB : ∀ (a : B) (w n m : Nat), lastLvl a = w → nfLe m a = true →
    stdIn a = true → stdIn (rwB w n a) = true := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ h; exact h
  | nd v0 s a1 _ iha =>
    intro w n m hll hnf hst
    obtain ⟨_, _, hnf1⟩ := (nfLe_nd_iff m v0 s a1).mp hnf
    have hst4 : (stdIn s && nonIncr a1 && visOK v0 a1 a1 && stdIn a1) = true := hst
    obtain ⟨hst123, hsta1⟩ := (Bool.and_eq_true _ _).mp hst4
    obtain ⟨hst12, hvisa1⟩ := (Bool.and_eq_true _ _).mp hst123
    obtain ⟨hsts, hnia1⟩ := (Bool.and_eq_true _ _).mp hst12
    cases a1 with
    | nil => exact hst
    | nd u2 s2 c2 =>
      have hll2 : lastLvl (B.nd u2 s2 c2) = w := by rw [← lastLvl_nd v0 s u2 s2 c2]; exact hll
      have hne2 : (B.nd u2 s2 c2) ≠ .nil := by intro hc; exact B.noConfusion hc
      rw [rwB_nd]
      by_cases h1 : hasLowAnc w (B.nd u2 s2 c2) = true
      · rw [if_pos h1]
        have hIH : stdIn (rwB w n (B.nd u2 s2 c2)) = true :=
          iha w n (v0 + 1) hll2 hnf1 hsta1
        rw [stdIn_nd_eq, hsts, nonIncr_rwB _ w n hll2 hnia1,
          visOK_self_rwB _ w n (v0 + 1) v0 hll2 hnf1 hIH hvisa1, hIH]
        rfl
      · rw [if_neg h1]
        have hLA2 : hasLowAnc w (B.nd u2 s2 c2) = false := by
          cases hd : hasLowAnc w (B.nd u2 s2 c2) with
          | false => rfl
          | true => exact absurd hd h1
        by_cases h2 : v0 < w
        · rw [if_pos h2, appB_iterD]
          have hvw : v0 + 1 = w := by
            have := lowAnc_lvl w (B.nd u2 s2 c2) (v0 + 1) hne2 hLA2 hll2 hnf1
            omega
          have hv : v0 < lastLvl (B.nd u2 s2 c2) := by rw [hll2]; exact h2
          have hGst : stdIn (GG v0 (B.nd u2 s2 c2) n) = true :=
            stdIn_GG v0 _ w hvw hne2 hLA2 hll2 hnia1 hsta1 hvisa1 n
          rw [stdIn_nd_eq, hsts, nonIncr_GG v0 _ hne2 hv hnia1 n,
            visOK_self_GG v0 _ w hvw hne2 hLA2 hll2 hvisa1 n hGst, hGst]
          rfl
        · rw [if_neg h2]; exact hst

/-! ### §62.10 主定理と、狭めた領域 -/

/-- **`stdB` は `repB` で閉じている。** `nfB` は §19、残る 2 つが §62 の内容。 -/
theorem stdB_repB (t : B) (n : Nat) (h : stdB t = true) : stdB (repB t n) = true := by
  have h1 : nfB t = true := nfB_of_stdB t h
  have h2 : nonIncr t = true := nonIncr_of_stdB t h
  have h3 : stdIn t = true := stdIn_of_stdB t h
  show (nfB (repB t n) && nonIncr (repB t n) && stdIn (repB t n)) = true
  rw [show nfB (repB t n) = true from nfLe_repB t 0 n h1,
    nonIncr_repB t n h2, stdIn_repB t n h3]
  rfl

/-- **`stdB` は `rwB` で閉じている。** -/
theorem stdB_rwB (t : B) (w n : Nat) (hll : lastLvl t = w) (h : stdB t = true) :
    stdB (rwB w n t) = true := by
  have h1 : nfB t = true := nfB_of_stdB t h
  have h2 : nonIncr t = true := nonIncr_of_stdB t h
  have h3 : stdIn t = true := stdIn_of_stdB t h
  show (nfB (rwB w n t) && nonIncr (rwB w n t) && stdIn (rwB w n t)) = true
  rw [show nfB (rwB w n t) = true from nfLe_rwB t w n 0 h1,
    nonIncr_rwB t w n hll h2, stdIn_rwB t w n 0 hll h1 h3]
  rfl

/-- **主定理。標準性は基本列で閉じている。** §61 の (i) が定理になった。 -/
theorem stdB_fsB (t : B) (h : stdB t = true) (n : Nat) : stdB (fsB t n) = true := by
  cases t with
  | nil => exact rfl
  | nd v r a =>
    cases v with
    | zero =>
      cases a with
      | nil => exact stdB_pred r h
      | nd u s c =>
        show stdB (if (lastLvl (B.nd u s c) == 0) = true
          then repB (B.nd 0 r (B.nd u s c)) n
          else rwB (lastLvl (B.nd u s c)) n (B.nd 0 r (B.nd u s c))) = true
        by_cases hz : (lastLvl (B.nd u s c) == 0) = true
        · rw [if_pos hz]; exact stdB_repB _ n h
        · rw [if_neg hz]
          exact stdB_rwB _ (lastLvl (B.nd u s c)) n rfl h
    | succ k =>
      cases a with
      | nil => exact rfl
      | nd u s c =>
        show stdB (if (lastLvl (B.nd u s c) == 0) = true
          then repB (B.nd (k + 1) r (B.nd u s c)) n
          else rwB (lastLvl (B.nd u s c)) n (B.nd (k + 1) r (B.nd u s c))) = true
        by_cases hz : (lastLvl (B.nd u s c) == 0) = true
        · rw [if_pos hz]; exact stdB_repB _ n h
        · rw [if_neg hz]
          exact stdB_rwB _ (lastLvl (B.nd u s c)) n rfl h

/-- **`certIn_region` の第 1 供給、狭めた領域で。** -/
theorem hclosedS_supply : ∀ (S : Matrix), RegS S → ∀ (n : Nat), RegS (BMS.expand S n) := by
  rintro S ⟨t, hstd, rfl⟩ n
  cases t with
  | nil =>
    refine ⟨.nil, rfl, ?_⟩
    show ((BMS.expand? [] n).getD []) = []
    rfl
  | nd v r a =>
    refine ⟨fsB (B.nd v r a) n, stdB_fsB _ hstd n, ?_⟩
    show ((BMS.expand? (matB (B.nd v r a) 0) n).getD []) = _
    rw [expand_matB (B.nd v r a) (topOKB_of_nfB _ (nfB_of_stdB _ hstd))
      (by intro hc; exact B.noConfusion hc) n]
    rfl

/-! ### §62.11 測定 (凍結)

否定的なものから。`C1_repB` の素朴な `plugB` 版は**偽**で、これが §62.8–§62.9 が
基準を据え置く形の帰納になっている理由。 -/

-- **否定。** `C1_repB` の素朴な `plugB` 版は偽。最小の反例。
#guard
  (let a : B := .nd 1 .nil .nil                      -- ψ₁(0)
   let x : B := .nd 0 .nil (.nd 1 .nil .nil)         -- ψ₀(ψ₁(0))
   let g : B := plugB a (iterD 0 a 2)
   nonIncr x && stdIn x && decide (sizeB x < sizeB g)
     && (cmpS (toL x) (toL a) == Ordering.lt)
     && !(cmpS (toL x) (toL g) == Ordering.lt)
     && !(visOK 0 x x))                              -- これが落ちている側条件
#guard matB (.nd 1 (.nil : B) .nil) 0 == [[0, 1]]
#guard matB (.nd 0 (.nil : B) (.nd 1 .nil .nil)) 0 == [[0, 0], [1, 1]]

-- 肯定。§61 の (i) は定理になったが、受領として再測定を残す。
#guard (enumB 3 6).all fun t => !(stdB t) || (List.range 6).all fun n => stdB (fsB t n)
#guard (enumB 4 5).all fun t => !(stdB t) || (List.range 6).all fun n => stdB (fsB t n)
-- 二つの枝の内訳 (`repB` 側 / `rwB` 側)。
#guard ((enumB 3 6).filter fun t => stdB t && lastLvl t == 0).length == 741
#guard ((enumB 3 6).filter fun t => stdB t).length == 1105
#guard ((popNFB 3 6).filter fun t => stdB t && lastLvl t == 0).length == 161
#guard ((popNFB 3 6).filter stdB).length == 235
-- 326 行目の添字とその基本列。
#guard match decodeB [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]] with
  | none => false
  | some t => stdB t && (List.range 6).all fun n => stdB (fsB t n)

-- **task 3 の測定。** `dict (bplus x y) = plus (dict x) (dict y)` は
-- `popNFB 3 6` の値の上で反例なし。**測定のみ、証明されていない。**
#guard (((popNFB 3 6).map bVal).eraseDups.take 40).all fun x =>
  (((popNFB 3 6).map bVal).eraseDups.take 40).all fun y =>
    Trans.Dict.dict (bplus x y) == TM.Term.plus (Trans.Dict.dict x) (Trans.Dict.dict y)
#guard (((popNFB 3 6).map bVal).eraseDups.take 80).all fun x =>
  Trans.Dict.dict (bplus x (BT.D 0 BT.zero)) == TM.Term.plus (Trans.Dict.dict x) TM.Term.one
-- `plus` の結合則が要るが、この repo の唯一のものは `CNV` を要求し、
-- 標準な値 235 個のうち `CNV` は 150 個しかない。
#guard (((popNFB 3 6).filter stdB).filter fun t => Evidence.WF.CNV (vOf t)).length == 150

/-! ### 公理の確認 -/

end

/-! ## §63 `plus` IS ASSOCIATIVE ON 𝔗(M), NOT ONLY ON THE VEBLEN FRAGMENT

`Evidence/CNVOps.lean` §19 proves `plus (plus a b) c = plus a (plus b c)` under `CNV`.
`CNV` admits only `zero`, `phi` and `add`, so it is the VEBLEN FRAGMENT and it excludes every
value that contains a `psi` or a `Z` — 85 of the 235 standard region values (§62.11's
`#guard`).  That is why §62 could not prove `dict (bplus x y) = plus (dict x) (dict y)` and had
to freeze it as a measurement.

WHAT THE §19 PROOF ACTUALLY USES.  Two things, and neither of them is `CNV`:

    (a) the components of a sum are additively principal and DESCEND;
    (b) `le` is transitive on the components.

`inT` says (a) verbatim — [Rathjen, 1991] 2.1(iii) is exactly `a.isAP && inT a && inT b` plus
`hdLe b a` — and §8.5.4 of `Evidence/WF.lean` says (b) verbatim: `le_trans_inT`.  So the whole
of §19 goes through one notch up, and this section restates it there.

MEASURED FIRST (all frozen as `#guard`s below).  Negative results first:

  * (a) is NOT optional.  With additively principal components but the DESCENT DROPPED the
    equation is false; the smallest counterexample found is `a = ω`, `b = 1 ⊕ ε₀`, `c = ω`
    (degree sum 19).  A component `zero` breaks it even sooner: `a = 1`, `b = 0 ⊕ ω`, `c = 1`.
  * (b) is NOT optional either, and this is the part that says `inT` — not merely "AP
    components, descending" — is the right hypothesis.  Over sums built from `ψ_M M`
    and `φ̄(ψ_M M)M` (terms that are AP, descending, and NOT `inT`, and on which §8.5.5's
    asymmetry counterexample lives) the equation FAILS.  So the structural condition alone
    is not enough: the components have to be genuinely comparable, and in this repository
    that is `FragR`, of which `inT` is the client-facing form.

  * POSITIVE: on all `inT` triples of two independent populations — the region's own 257
    distinct values `vOf` over `popNFB 3 6` (40³ triples measured, 25³ frozen below) and a
    hand enumeration of sums over `{1, ω, ε₀, Ω, Γ₀, ψ_{Z0}(Z1), Z1, M, ω^(M⊕1)}` (100³
    triples, frozen below) — zero counterexamples.

WHAT IS RESTATED.  Only what §63 itself needs, and each one is the §19 proof with `CNV`
replaced by `inT` and `frag_of_cnv`/`le_trans` replaced by `le_trans_inT`:
`inT_toList`, `inT_ofList_toList`, `filter_eq_take_inT`, `toList_plus_inT`,
`filter_nil_of_head_inT`, `inT_plus`, `plus_assoc_inT`.  `lt_ofList` (§20) is NOT restated —
§63 never reads the order off the component list.

WHAT IS NOT CLAIMED.  Nothing here says anything about `dict`, about `collapse`, or about the
values of the region; those are §63.3 and §63.4 below, and §63.4 does NOT close.
-/

section
open Trans.Recal
open Trans.Dict (BT)
open TM TM.Term
open Evidence.WF

/-! ### §63.1 `plus` の結合則、`inT` の上で -/

/-- 成分がすべて加法主要かつ `inT` か (`cnvL` の `inT` 版)。 -/
def inTL (l : List Term) : Bool := l.all (fun x => x.isAP && inT x)

theorem inTL_cons {a : Term} {l : List Term} :
    inTL (a :: l) = true ↔ (a.isAP = true ∧ inT a = true) ∧ inTL l = true := by
  constructor
  · intro h
    have h' := (List.all_cons ..).symm.trans h
    have h2 := (Bool.and_eq_true _ _).mp h'
    exact ⟨(Bool.and_eq_true _ _).mp h2.1, h2.2⟩
  · intro ⟨⟨h1, h2⟩, h3⟩
    show ((a.isAP && inT a) && inTL l) = true
    rw [h1, h2, h3]
    rfl

theorem inTL_take (k : Nat) (l : List Term) (h : inTL l = true) : inTL (l.take k) = true := by
  show (l.take k).all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_of_mem_take hx)

/-- [Rathjen, 1991] 2.1(iii) を `hdLe` で書き直す。最後の連言はちょうど `hdLe b a`。 -/
theorem inT_add_eq (a b : Term) :
    inT (add a b) = (a.isAP && inT a && inT b && hdLe b a) := by
  show (a.isAP && inT a && inT b &&
      (match b with | add c _ => le c a | _ => b.isAP && le b a)) = _
  cases b with
  | zero => rfl
  | add _ _ => rfl
  | M => rfl | omg _ => rfl | phi _ _ => rfl | psi _ _ => rfl | Z _ => rfl

theorem inT_add {a b : Term} (h : inT (add a b) = true) :
    a.isAP = true ∧ inT a = true ∧ inT b = true ∧ hdLe b a = true := by
  rw [inT_add_eq] at h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h1
  obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
  exact ⟨h5, h6, h4, h2⟩

/-- **𝔗(M) の項は、降順の加法主要成分の列。**  §19 の `cnv_toList` の `inT` 版。 -/
theorem inT_toList : ∀ (t : Term), inT t = true →
    inTL (toList t) = true ∧ descL (toList t) = true := by
  intro t
  induction t with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | M => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | omg a _ => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | phi a b _ _ => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | psi k a _ _ => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | Z a _ => intro h; exact ⟨inTL_cons.mpr ⟨⟨rfl, h⟩, rfl⟩, rfl⟩
  | add a b _ ihb =>
    intro h
    obtain ⟨hap, hia, hib, hhd⟩ := inT_add h
    obtain ⟨hcl, hdl⟩ := ihb hib
    have he : toList (add a b) = a :: toList b := rfl
    rw [he]
    refine ⟨inTL_cons.mpr ⟨⟨hap, hia⟩, hcl⟩, ?_⟩
    cases hb : toList b with
    | nil => rfl
    | cons c rest =>
      refine descL_cons.mpr ⟨?_, by rw [← hb]; exact hdl⟩
      rw [← hdLe_eq_of_toList (a := a) hb]
      exact hhd

theorem inTL_isAP {t : Term} (h : inT t = true) : ∀ x ∈ toList t, x.isAP = true := by
  intro x hx
  exact ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp (inT_toList t h).1 x hx)).1

theorem inTL_inT {t : Term} (h : inT t = true) : ∀ x ∈ toList t, inT x = true := by
  intro x hx
  exact ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp (inT_toList t h).1 x hx)).2

/-- 成分列から組み直す。`hdLe` が `b ≠ zero` を保証する。 -/
theorem inT_ofList_toList : ∀ (t : Term), inT t = true → ofList (toList t) = t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | M => intro _; rfl
  | omg _ _ => intro _; rfl
  | phi _ _ _ _ => intro _; rfl
  | psi _ _ _ _ => intro _; rfl
  | Z _ _ => intro _; rfl
  | add a b _ ihb =>
    intro h
    obtain ⟨_, _, hib, hhd⟩ := inT_add h
    have hbz : b ≠ zero := by
      intro hz; rw [hz] at hhd; exact Bool.noConfusion hhd
    show ofList (a :: toList b) = add a b
    cases hbl : toList b with
    | nil => exact absurd (toList_eq_nil b hbl) hbz
    | cons c u =>
      show add a (ofList (c :: u)) = add a b
      rw [← hbl, ihb hib]

theorem lt_of_not_le_inT {a b : Term} (ha : inT a = true) (hb : inT b = true)
    (h : le a b = false) : lt b a = true :=
  lt_of_not_le3 (inT_le_fragR a ha) (inT_le_fragR b hb) h

/-- 降順の列で `le b₁ ·` を通すのは、前を切り取るのと同じ (§17 の `inT` 版)。 -/
theorem filter_eq_take_inT : ∀ (b1 : Term) (l : List Term), inTL l = true → descL l = true →
    inT b1 = true → ∃ k, l.filter (fun a => le b1 a) = l.take k := by
  intro b1 l
  induction l with
  | nil => intro _ _ _; exact ⟨0, rfl⟩
  | cons a t ih =>
    intro hc hd hb1
    obtain ⟨⟨_, hia⟩, hct⟩ := inTL_cons.mp hc
    cases hle : le b1 a with
    | true =>
      obtain ⟨k, hk⟩ := ih hct (descL_tail hd) hb1
      refine ⟨k + 1, ?_⟩
      rw [List.filter_cons_of_pos (by rw [hle]), hk]
      rfl
    | false =>
      refine ⟨0, ?_⟩
      rw [List.filter_cons_of_neg (by rw [hle]; exact Bool.noConfusion)]
      have hnil : ∀ (u : List Term), inTL u = true → descL (a :: u) = true →
          u.filter (fun x => le b1 x) = [] := by
        intro u
        induction u with
        | nil => intro _ _; rfl
        | cons c v ihv =>
          intro hcu hdu
          obtain ⟨⟨_, hicv⟩, hcv⟩ := inTL_cons.mp hcu
          have hca' : le c a = true := (descL_cons.mp hdu).1
          have hnc : le b1 c = false := by
            cases hbc : le b1 c with
            | false => rfl
            | true =>
              exact absurd (le_trans_inT hb1 hicv hia hbc hca')
                (by rw [hle]; exact Bool.noConfusion)
          rw [List.filter_cons_of_neg (by rw [hnc]; exact Bool.noConfusion)]
          refine ihv hcv ?_
          cases v with
          | nil => rfl
          | cons d w =>
            refine descL_cons.mpr ⟨?_, descL_tail (descL_tail hdu)⟩
            exact le_trans_inT (inTL_cons.mp hcv).1.2 hicv hia
              (descL_cons.mp (descL_tail hdu)).1 hca'
      exact hnil t hct hd

/-- 先頭より上のものは、その後ろにも無い (§19 の `filter_nil_of_head` の `inT` 版)。 -/
theorem filter_nil_of_head_inT {b1 : Term} (hb1 : inT b1 = true) :
    ∀ (a : Term) (u : List Term), inT a = true → inTL u = true → descL (a :: u) = true →
      le b1 a = false → (a :: u).filter (fun x => le b1 x) = [] := by
  intro a u hia hcu hd hle
  rw [List.filter_cons_of_neg (by rw [hle]; exact Bool.noConfusion)]
  have hnil : ∀ (v : List Term), inTL v = true → descL (a :: v) = true →
      v.filter (fun x => le b1 x) = [] := by
    intro v
    induction v with
    | nil => intro _ _; rfl
    | cons c w ihw =>
      intro hcv hdv
      obtain ⟨⟨_, hicv⟩, hcw⟩ := inTL_cons.mp hcv
      have hca' : le c a = true := (descL_cons.mp hdv).1
      have hnc : le b1 c = false := by
        cases hbc : le b1 c with
        | false => rfl
        | true =>
          exact absurd (le_trans_inT hb1 hicv hia hbc hca')
            (by rw [hle]; exact Bool.noConfusion)
      rw [List.filter_cons_of_neg (by rw [hnc]; exact Bool.noConfusion)]
      refine ihw hcw ?_
      cases w with
      | nil => rfl
      | cons d z =>
        refine descL_cons.mpr ⟨?_, descL_tail (descL_tail hdv)⟩
        exact le_trans_inT (inTL_cons.mp hcw).1.2 hicv hia
          (descL_cons.mp (descL_tail hdv)).1 hca'
  exact hnil u hcu hd

/-- `plus` の成分列 (§19 の `toList_plus` の `inT` 版)。 -/
theorem toList_plus_inT {s t : Term} (hs : inT s = true) (ht : inT t = true)
    {b1 : Term} {rest : List Term} (hl : toList t = b1 :: rest) :
    toList (plus s t) = (toList s).filter (fun a => le b1 a) ++ toList t := by
  have hall : ∀ x ∈ (toList s).filter (fun a => le b1 a) ++ toList t, x.isAP = true := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact inTL_isAP hs x ((List.mem_filter.mp h).1)
    · exact inTL_isAP ht x h
  show toList (match toList t with
      | [] => s
      | b :: _ => ofList ((toList s).filter (fun a => le b a) ++ toList t)) = _
  rw [hl]
  show toList (ofList ((toList s).filter (fun a => le b1 a) ++ (b1 :: rest))) = _
  rw [hl] at hall
  rw [toList_ofList _ hall]

/-- **`plus` は 𝔗(M) の上で結合的。**  §19 `plus_assoc` の `CNV` を `inT` に落としたもの。 -/
theorem plus_assoc_inT (a b c : Term) (ha : inT a = true) (hb : inT b = true)
    (hc : inT c = true) : plus (plus a b) c = plus a (plus b c) := by
  obtain ⟨hca, hda⟩ := inT_toList a ha
  obtain ⟨hcb, hdb⟩ := inT_toList b hb
  obtain ⟨hcc, hdc⟩ := inT_toList c hc
  cases hC : toList c with
  | nil =>
    have hcz : c = zero := toList_eq_nil c hC
    rw [hcz]
    show plus (plus a b) zero = plus a (plus b zero)
    rfl
  | cons c1 C' =>
    rw [hC] at hcc hdc
    obtain ⟨⟨_, hic1⟩, _⟩ := inTL_cons.mp hcc
    cases hB : toList b with
    | nil =>
      have hbz : b = zero := toList_eq_nil b hB
      have h1 : plus a b = a := by rw [hbz]; rfl
      have h2 : plus b c = c := by
        rw [plus_eq (s := b) hC, hB]
        show ofList (([] : List Term) ++ toList c) = c
        show ofList (toList c) = c
        exact inT_ofList_toList c hc
      rw [h1, h2]
    | cons b1 B' =>
      rw [hB] at hcb hdb
      obtain ⟨⟨_, hib1⟩, hcB'⟩ := inTL_cons.mp hcb
      have hab : toList (plus a b) = (toList a).filter (fun x => le b1 x) ++ toList b :=
        toList_plus_inT ha hb hB
      have hbc : toList (plus b c) = (toList b).filter (fun x => le c1 x) ++ toList c :=
        toList_plus_inT hb hc hC
      have hL : plus (plus a b) c
          = ofList ((((toList a).filter (fun x => le b1 x) ++ toList b).filter
              (fun x => le c1 x)) ++ toList c) := by
        rw [plus_eq (s := plus a b) hC, hab]
      cases hcb1' : le c1 b1 with
      | true =>
        have hkeep : ((toList a).filter (fun x => le b1 x)).filter (fun x => le c1 x)
            = (toList a).filter (fun x => le b1 x) := by
          refine filter_self_of_all _ _ ?_
          intro x hx
          have hbx : le b1 x = true := (List.mem_filter.mp hx).2
          have hix : inT x = true := inTL_inT ha x (List.mem_filter.mp hx).1
          exact le_trans_inT hic1 hib1 hix hcb1' hbx
        have hhead : (toList b).filter (fun x => le c1 x)
            = b1 :: B'.filter (fun x => le c1 x) := by
          rw [hB]; exact List.filter_cons_of_pos (by rw [hcb1'])
        have hbc' : toList (plus b c)
            = b1 :: (B'.filter (fun x => le c1 x) ++ toList c) := by
          rw [hbc, hhead]; rfl
        rw [hL, plus_eq (s := a) hbc', hbc, List.filter_append, hkeep, hhead,
          List.append_assoc]
      | false =>
        have hbn : (toList b).filter (fun x => le c1 x) = [] := by
          rw [hB]; exact filter_nil_of_head_inT hic1 b1 B' hib1 hcB' hdb hcb1'
        have hswap : ((toList a).filter (fun x => le b1 x)).filter (fun x => le c1 x)
            = (toList a).filter (fun x => le c1 x) := by
          refine filter_of_imp _ _ _ ?_
          intro x hx hcx
          have hix : inT x = true := inTL_inT ha x hx
          have hbc1 : le b1 c1 = true := by
            have h1 : lt b1 c1 = true := lt_of_not_le_inT hic1 hib1 hcb1'
            show (b1 == c1 || lt b1 c1) = true
            rw [h1]
            exact Bool.or_true _
          exact le_trans_inT hib1 hic1 hix hbc1 hcx
        have hbc' : toList (plus b c) = c1 :: C' := by
          rw [hbc, hbn, hC]; rfl
        rw [hL, plus_eq (s := a) hbc', hbc, List.filter_append, hswap, hbn,
          List.append_nil, List.nil_append]

/-! ### §63.2 `plus` の閉包、`0 ⊕ ·`、`· ⊕ 1`

§17 の `cnv_plus` と §21 の `lt_plus_left` のうち §63 が使う分だけ。`lt_plus_left` は
§20 の `lt_ofList` を経由するが、`lt_ofList` は `eq_phi_of_isAP_cnv`(「`CNV` の加法主要項は
`φ̄`」) を使うので `inT` へはそのままでは上がらない。ここで要るのは `x = 1` の場合だけなので、
`Evidence/Cert.lean` §15.1 の一般加法主要版の節 (`lt_ap_add`, `plus_one_add`, `le_one_ap`) を
使って和の長さの帰納で直接示す。§20 は復元していない。 -/

theorem inT_ofList : ∀ (l : List Term), inTL l = true → descL l = true →
    inT (ofList l) = true
  | [], _, _ => rfl
  | [a], h, _ => (inTL_cons.mp h).1.2
  | a :: b :: t, h, hd => by
    obtain ⟨⟨hap, hia⟩, hrest⟩ := inTL_cons.mp h
    obtain ⟨hle, hd2⟩ := descL_cons.mp hd
    have hbap : b.isAP = true := (inTL_cons.mp hrest).1.1
    show inT (add a (ofList (b :: t))) = true
    rw [inT_add_eq, hap, hia, inT_ofList (b :: t) hrest hd2, hdLe_ofList hbap, hle]
    rfl

/-- **𝔗(M) は `plus` で閉じる。** §17 の `cnv_plus` の `inT` 版。 -/
theorem inT_plus {s t : Term} (hs : inT s = true) (ht : inT t = true) :
    inT (plus s t) = true := by
  obtain ⟨hcs, hds⟩ := inT_toList s hs
  obtain ⟨hct, hdt⟩ := inT_toList t ht
  show inT (match toList t with
            | [] => s
            | b1 :: _ => ofList ((toList s).filter (fun a => le b1 a) ++ toList t)) = true
  cases hl : toList t with
  | nil => exact hs
  | cons b1 rest =>
    rw [hl] at hct hdt
    obtain ⟨⟨_, hb1⟩, _⟩ := inTL_cons.mp hct
    obtain ⟨k, hk⟩ := filter_eq_take_inT b1 (toList s) hcs hds hb1
    show inT (ofList ((toList s).filter (fun a => le b1 a) ++ (b1 :: rest))) = true
    rw [hk]
    refine inT_ofList _ ?_ ?_
    · show ((toList s).take k ++ (b1 :: rest)).all _ = true
      rw [List.all_eq_true]
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact List.all_eq_true.mp (inTL_take k (toList s) hcs) x h
      · exact List.all_eq_true.mp hct x h
    · refine descL_append _ _ (descL_take k (toList s) hds) hdt ?_
      intro a b w ha hb
      injection hb with hb1eq _
      rw [← hb1eq]
      have hmem : a ∈ (toList s).filter (fun x => le b1 x) := by
        rw [hk]; exact getLast?_mem ha
      exact (List.mem_filter.mp hmem).2

/-- `0` は `plus` の左単位 (成分から組み直せる項の上で)。 -/
theorem plus_zero_left_inT {t : Term} (ht : inT t = true) : plus zero t = t := by
  cases hl : toList t with
  | nil => rw [toList_eq_nil t hl]; rfl
  | cons b1 rest =>
    rw [plus_eq (s := zero) hl]
    show ofList (([] : List Term) ++ toList t) = t
    rw [List.nil_append]
    exact inT_ofList_toList t ht

/-- **`v < v ⊕ 1`。** 和の長さの帰納。 -/
theorem lt_self_plus_one_inT : ∀ (v : Term), inT v = true → lt v (plus v one) = true := by
  intro v
  induction v with
  | zero => intro _; exact rfl
  | M => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl M one]; exact Evidence.WF.le_self M
  | omg a _ => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl (omg a) one]; exact Evidence.WF.le_self (omg a)
  | phi a b _ _ => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl (phi a b) one]; exact Evidence.WF.le_self (phi a b)
  | psi k a _ _ => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl (psi k a) one]; exact Evidence.WF.le_self (psi k a)
  | Z a _ => intro _; rw [Evidence.Cert.plus_one_ap rfl (Evidence.Cert.le_one_ap rfl),
      Evidence.Cert.lt_ap_add rfl (Z a) one]; exact Evidence.WF.le_self (Z a)
  | add a b _ ihb =>
    intro h
    obtain ⟨hap, _, hib, _⟩ := inT_add h
    have hone : le one a = true := Evidence.Cert.le_one_ap hap
    have hrec : lt b (plus b one) = true := ihb hib
    have hne : b ≠ plus b one := by
      intro hc; rw [← hc, Evidence.WF.lt_irrefl] at hrec; exact Bool.noConfusion hrec
    rw [Evidence.Cert.plus_one_add hone,
      Evidence.WF.lt_add_add (by intro hc; injection hc with _ h2; exact hne h2), if_pos rfl]
    exact hrec

end

/-! ## §63.3 `dict` DISTRIBUTES OVER `bplus`

`bplus x y` is `BT.ofL (x.toL ++ y.toL)` and `dict` is compositional over `.sum`
(`Trans/Dict.lean`'s `dict_sum`), so the content of

    dict (bplus x y) = plus (dict x) (dict y)

is the `toL`/`ofL` round trip of §53 plus §63.1's associativity.  §62.11 measured the equation
with ZERO counterexamples and NO side condition (40×40 region values, and the corollary on 80).

THE SIDE CONDITION THE PROOF NEEDS, HONESTLY.  Two, and neither is visible in the equation:

  * `NfSum x` and `NfSum y` (§53) — `ofL` is a section of `toL` only on terms already in
    that shape, so without it `dict (bplus x y)` and `plus (dict x) (dict y)` are statements
    about different terms.  `nfSum_bplus`/`nfSum_D`/`nfSum_zero` discharge it everywhere §63
    uses it, and `nfSum_bVal` below discharges it for the region's own values.
  * `inT (dict a) = true` for every component `a` of `x.toL ++ y.toL`.  This is where §63.1
    is consumed: the induction on `l1` peels one component and re-associates, and
    `plus_assoc_inT` wants all three arguments `inT`.  There is no way around it — §63.1's
    own measurement shows associativity is FALSE without it.

The second condition is not decoration either: `inT (dict ·)` is exactly the theorem this
repository does not have (`Evidence/RegionNext.lean` line 14637 and line 15126 both say so).
`CollapseInT` below isolates it to one line, and §63.4 carries it as a hypothesis rather than
pretending it is proved. -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term
open Trans.Dict (dict)

/-- 成分の像がすべて 𝔗(M) に入るなら、和の像も入る。 -/
theorem inT_dict_ofL : ∀ (l : List BT), (∀ x ∈ l, inT (dict x) = true) →
    inT (dict (BT.ofL l)) = true
  | [], _ => rfl
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
    show inT (dict (BT.sum a (BT.ofL (b :: t)))) = true
    rw [Trans.Dict.dict_sum]
    exact inT_plus (h a (List.Mem.head _))
      (inT_dict_ofL (b :: t) (fun z hz => h z (List.Mem.tail a hz)))

/-- **`dict` は成分列の連結を `plus` に送る。** §63.1 を消費するのはここ。 -/
theorem dict_ofL_append : ∀ (l1 l2 : List BT),
    (∀ x ∈ l1, inT (dict x) = true) → (∀ x ∈ l2, inT (dict x) = true) →
    dict (BT.ofL (l1 ++ l2)) = plus (dict (BT.ofL l1)) (dict (BT.ofL l2))
  | [], l2, _, h2 => by
    show dict (BT.ofL l2) = plus (dict BT.zero) (dict (BT.ofL l2))
    rw [show dict BT.zero = zero from rfl]
    exact (plus_zero_left_inT (inT_dict_ofL l2 h2)).symm
  | [a], l2, _, _ => by
    cases l2 with
    | nil => rfl
    | cons b t => exact Trans.Dict.dict_sum a (BT.ofL (b :: t))
  | a :: b :: t, l2, h1, h2 => by
    have hIH := dict_ofL_append (b :: t) l2 (fun z hz => h1 z (List.Mem.tail a hz)) h2
    show dict (BT.sum a (BT.ofL (b :: (t ++ l2))))
        = plus (dict (BT.sum a (BT.ofL (b :: t)))) (dict (BT.ofL l2))
    rw [Trans.Dict.dict_sum, Trans.Dict.dict_sum,
      show BT.ofL (b :: (t ++ l2)) = BT.ofL ((b :: t) ++ l2) from rfl, hIH]
    exact (plus_assoc_inT _ _ _ (h1 a (List.Mem.head _))
      (inT_dict_ofL (b :: t) (fun z hz => h1 z (List.Mem.tail a hz)))
      (inT_dict_ofL l2 h2)).symm

/-- **§63.3 の主定理。** -/
theorem dict_bplus (x y : BT) (hx : NfSum x) (hy : NfSum y)
    (hdx : ∀ a ∈ x.toL, inT (dict a) = true) (hdy : ∀ a ∈ y.toL, inT (dict a) = true) :
    dict (bplus x y) = plus (dict x) (dict y) := by
  show dict (BT.ofL (x.toL ++ y.toL)) = _
  rw [dict_ofL_append x.toL y.toL hdx hdy,
    show BT.ofL x.toL = x from hx, show BT.ofL y.toL = y from hy]

theorem dict_D0_zero : dict (BT.D 0 BT.zero) = one := by decide

theorem inT_one : inT one = true := by decide

/-- **`Hsucc` を開ける系。** -/
theorem dict_bplus_one (x : BT) (hx : NfSum x) (hdx : ∀ a ∈ x.toL, inT (dict a) = true) :
    dict (bplus x (BT.D 0 BT.zero)) = plus (dict x) one := by
  rw [dict_bplus x (BT.D 0 BT.zero) hx (nfSum_D 0 BT.zero) hdx
    (by intro a ha
        rw [List.mem_singleton.mp (show a ∈ [BT.D 0 BT.zero] from ha), dict_D0_zero]
        exact inT_one), dict_D0_zero]

end

/-! ## §63.4 THE VALUE HALF OF `Hsucc`, AND THE ONE FACT THAT IS MISSING

WHAT IS PROVED.  `vOf (nd 0 r nil) = plus (vOf r) 1` and `lt (vOf r) (vOf (nd 0 r nil))`, and
with §61's `hsuccS_index` the whole of `certIn_region`'s `Hsucc` supply for the narrowed
region — **conditionally on `CollapseInT`**.

WHAT IS NOT PROVED, AND IS NOT WEAKENED AWAY.  `CollapseInT` says

    ∀ u a, inT (dict (BT.D u a)) = true

— "the Buchholz collapse always lands in 𝔗(M)".  It is `Trans/Dict.lean`'s acceptance record
item (B), which that file states only as `#guard`s over three corpora.  It is MEASURED here
too (see the `#guard`s below): 1805 `BT` terms of a systematic enumeration that does NOT
filter by `BT.isStd`, and the 443 distinct components of `bVal` over `popNFB 3 6`, with zero
counterexamples.  Restricting it to `BT.isStd` would be WRONG for this client: the 443
components of the region's own values are not all `isStd` (measured below).

Proving it means proving `inT (collapse u x)` — the whole of `wcnf`/`mulL`/`divAP`/`phiNF`
and, for the strongly critical branch, [Rathjen, 1991] 2.1(vi)'s `(Kset κ α).all (· < α)`.
That is a section of its own and none of it is attempted here.

AND INDUCTING ON THE INDEX DOES NOT DODGE IT.  `inT_vOf` below is proved by structure on `B`
and needs no `stdB`, but the induction bottoms out at the components of `bVal t`, which
`atomsL_bVal` (§53) says are exactly the `BT.D w (bArg w c)` — and `dict` is NOT compositional
through `.D`: `dict (.D u a) = collapse u (dict a)` throws away the Buchholz syntax.  So the
index-side induction reaches the same wall from the other side; there is no region-restricted
version of item 3 that is cheaper than `inT (collapse ·)` itself.  Everything below therefore
takes `CollapseInT` as an explicit hypothesis, and `hsuccS_supply` cannot be handed to
`certIn_region` until it is discharged. -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT)
open TM TM.Term
open Trans.Dict (dict)

/-- **欠けている 1 つの事実。** Buchholz の崩壊の像が 𝔗(M) に入ること。証明されていない。 -/
def CollapseInT : Prop := ∀ (u : Nat) (a : BT), inT (dict (BT.D u a)) = true

-- `nfSum_bVal` (§56) と `atomsL_bVal` (§53) は既にある。ここで使う。

theorem dictAtoms_bVal (H : CollapseInT) (t : B) :
    ∀ a ∈ (bVal t).toL, inT (dict a) = true := by
  intro a ha
  obtain ⟨u, b, rfl⟩ := atomsL_bVal t a ha
  exact H u b

theorem inT_dict_bVal (H : CollapseInT) (t : B) : inT (dict (bVal t)) = true := by
  have h := inT_dict_ofL (bVal t).toL (dictAtoms_bVal H t)
  rwa [show BT.ofL (bVal t).toL = bVal t from nfSum_bVal t] at h

/-- **§63 の項目 3。** 領域の値は 𝔗(M) の項 — `CollapseInT` を仮定して、しかし `stdB` は不要。 -/
theorem inT_vOf (H : CollapseInT) (t : B) : inT (vOf t) = true := by
  cases t with
  | nil => exact rfl
  | nd w r c =>
    show inT (plus one (dict (bVal (B.nd w r c)))) = true
    exact inT_plus inT_one (inT_dict_bVal H _)

/-- **§63 の項目 4 の値の等式。** -/
theorem vOf_succ (H : CollapseInT) (r : B) : vOf (.nd 0 r .nil) = plus (vOf r) one := by
  cases r with
  | nil => exact rfl
  | nd w s c =>
    show plus one (dict (bVal (B.nd 0 (B.nd w s c) B.nil)))
        = plus (plus one (dict (bVal (B.nd w s c)))) one
    rw [show bVal (B.nd 0 (B.nd w s c) B.nil)
          = bplus (bVal (B.nd w s c)) (BT.D 0 BT.zero) from rfl,
      dict_bplus_one _ (nfSum_bVal _) (dictAtoms_bVal H _)]
    exact (plus_assoc_inT _ _ _ inT_one (inT_dict_bVal H _) inT_one).symm

theorem lt_vOf_succ (H : CollapseInT) (r : B) : lt (vOf r) (vOf (.nd 0 r .nil)) = true := by
  rw [vOf_succ H r]
  exact lt_self_plus_one_inT (vOf r) (inT_vOf H r)

/-- **`certIn_region` の `Hsucc` 供給、狭めた領域で。** `CollapseInT` に依存する。 -/
theorem hsuccS_supply (H : CollapseInT) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS (BMS.expand S n) u := by
  intro S v hreg hval hk
  obtain ⟨r, hv, _, hexp⟩ := hsuccS_index S v hreg hval hk
  refine ⟨vOf r, ?_, ?_, inT_vOf H r, ?_, fun n => (hexp n).2⟩
  · rw [hv]; exact vOf_succ H r
  · rw [hv]; exact inT_vOf H _
  · rw [hv]; exact lt_vOf_succ H r

end

/-! ## §63.5 MEASURED (frozen)

Negative results first: the three ways `plus (plus a b) c = plus a (plus b c)` fails, one per
conjunct of the hypothesis it is proved under.  The third is the one that decides the design —
it says the hypothesis has to be `inT` and not merely "additively principal components,
descending", because the order is not even TOTAL outside `FragR`. -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Trans.Dict (BT)

-- **否定 1.** 成分に `zero` が混ざると落ちる。`a = 1`, `b = 0 ⊕ ω`, `c = 1`。
#guard !((TM.Term.toList (add zero omega)).all (fun x => x.isAP))
#guard TM.Term.plus (TM.Term.plus one (add zero omega)) one
       != TM.Term.plus one (TM.Term.plus (add zero omega) one)

-- **否定 2.** 成分は加法主要でも、降順でないと落ちる。`a = ω`, `b = 1 ⊕ ε₀`, `c = ω` (次数和 19)。
#guard (TM.Term.toList (add one (phi one zero))).all (fun x => x.isAP)
#guard !(Evidence.WF.descL (TM.Term.toList (add one (phi one zero))))
#guard TM.Term.plus (TM.Term.plus omega (add one (phi one zero))) omega
       != TM.Term.plus omega (TM.Term.plus (add one (phi one zero)) omega)

-- **否定 3.** 加法主要かつ降順でも `inT` でないと落ちる。`a = c = ψ_M M`, `b = ψ_{ψ_M M} 0`
--   (次数和 11)。この 2 つは **比較不能** — `lt` がどちらの向きにも `false` で、
--   `plus` の篩 `le b₁ ·` はそこで意味を失う。`WF` §8.5.5 と同じ場所。
#guard !(inT (psi M M)) && !(inT (psi (psi M M) zero))
#guard !(TM.Term.lt (psi M M) (psi (psi M M) zero))
     && !(TM.Term.lt (psi (psi M M) zero) (psi M M))
#guard (psi M M) != (psi (psi M M) zero)
#guard TM.Term.plus (TM.Term.plus (psi M M) (psi (psi M M) zero)) (psi M M)
       != TM.Term.plus (psi M M) (TM.Term.plus (psi (psi M M) zero) (psi M M))

-- 肯定 1.  領域の値そのもの。`vOf` の相異なる像は 257 個、その先頭 25 個で 25³ 三つ組。
#guard ((popNFB 3 6).map vOf).eraseDups.length == 257
#guard ((popNFB 3 6).map vOf).eraseDups.all fun x => TM.Term.inT x
#guard (((popNFB 3 6).map vOf).eraseDups.take 25).all fun a =>
  (((popNFB 3 6).map vOf).eraseDups.take 25).all fun b =>
    (((popNFB 3 6).map vOf).eraseDups.take 25).all fun c =>
      TM.Term.plus (TM.Term.plus a b) c == TM.Term.plus a (TM.Term.plus b c)
-- `CNV` はこの母集団の 159 個にしか成り立たない。§19 が届かない理由。
#guard (((popNFB 3 6).map vOf).eraseDups.filter fun x => Evidence.WF.CNV x).length == 159

-- 肯定 2.  ψ・Z の原子を含む手作りの母集団 (`{1, ω, ε₀, Ω, Γ₀, ψ_{Z0}(Z1), Z1, M, ω^(M⊕1)}`
--   から作った 0〜3 成分の和のうち `inT` なもの) で、全三つ組。
private def at63 : List TM.Term :=
  [one, omega, phi one zero, Z zero, psi (Z zero) zero, psi (Z zero) (Z one),
   Z one, M, omg (add M one)]
private def raw63 : List TM.Term :=
  [zero] ++ at63
  ++ (at63.flatMap fun a => at63.map fun b => add a b)
  ++ (at63.flatMap fun a => at63.map fun b => add a (add b one))
  ++ (at63.map fun a => add a zero) ++ (at63.map fun a => add zero a)
  ++ (at63.flatMap fun a => at63.map fun b => add (add a b) one)
private def in63 : List TM.Term := raw63.filter fun x => TM.Term.inT x
#guard at63.all fun x => TM.Term.inT x
#guard raw63.length == 271
#guard in63.length == 100
#guard in63.all fun a => in63.all fun b => in63.all fun c =>
  TM.Term.plus (TM.Term.plus a b) c == TM.Term.plus a (TM.Term.plus b c)

-- 肯定 3.  §63.3 の等式 (§62.11 の再掲)。
#guard (((popNFB 3 6).map bVal).eraseDups.take 25).all fun x =>
  (((popNFB 3 6).map bVal).eraseDups.take 25).all fun y =>
    Trans.Dict.dict (bplus x y) == TM.Term.plus (Trans.Dict.dict x) (Trans.Dict.dict y)

-- 肯定 4.  §63.4 が仮定する `CollapseInT` の測定。**証明ではない。**
--   (i) 領域の値の成分 443 個すべて。
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.length == 443
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.all fun a =>
  TM.Term.inT (Trans.Dict.dict a)
--   **`BT.isStd` に制限してはいけない。** 領域の成分は全部が標準ではない。
#guard !(((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.all fun a => BT.isStd a)
--   (ii) `isStd` で絞らない `BT` の系統的な列挙 1805 個。
private def bseed63 : List BT := [.zero, .D 0 .zero, .D 1 .zero, .D 2 .zero, .D 0 (.D 1 .zero)]
private def bstep63 (l : List BT) : List BT :=
  l ++ (List.range 3).flatMap (fun u => l.map (fun a => BT.D u a))
    ++ (l.flatMap fun a => l.map fun b => BT.sum a b)
private def bcorp63 : List BT := (bstep63 (bstep63 bseed63).eraseDups).eraseDups
#guard bcorp63.length == 1805
#guard bcorp63.all fun a => TM.Term.inT (Trans.Dict.dict a)

end


/-! ## §64 `collapse` LANDS IN 𝔗(M) — EVERY OPERATOR BUT TWO, AND THE TWO ARE NAMED

§63 closed `Hsucc` for the generalised region except for one hypothesis:

    CollapseInT : ∀ (u : Nat) (a : BT), inT (dict (BT.D u a)) = true

i.e. `inT (collapse u (dict a))`.  §64 takes it apart operator by operator.  What comes out
is that `collapse` is `inT` for EVERY operator it uses except two, and the two are isolated,
stated, and measured rather than assumed silently.

WHAT IS PROVED, UNCONDITIONALLY.

  §64.1  `lt · M` is STRUCTURAL: `lt t M = hdBelowM t`, where `hdBelowM` reads the head
         component and answers `false` only for `M` and `ω̄^·` ([Rathjen, 1991] 2.3.2/2.3.3).
         With it, `lt (ofList l) M`, `lt (plus s t) M` and "every component of a term below
         `M` is below `M`" are all one step.  This is the toolkit the rest of §64 runs on:
         2.1(v) asks `α, β < M` of every `φ̄` and nothing in §63 could supply it.

  §64.2  one `inT`-preservation lemma per operator, each with its `lt · M` twin:
         `sub1`, `subAP`, `logOm`, `divAP`, `phiNFdefault`, `phiNFsucc`, `phiNF`, `omegaNF`,
         `ofNat`, `splitFin`.  `inT_omegaNF` needs NO side condition (the `ω̄^·` branch
         carries `M < α` itself); `inT_phiNF` needs exactly 2.1(v)'s `α, β < M`.

  §64.3  the component-list toolkit: a descending list of `inT` terms is bounded by its head
         (`descL_bound_inT` — the only place `le_trans_inT` is used), hence filtering keeps
         it descending (`descL_filter_inT`).

  §64.4  `wcnf` returns components that are `inT` and below `M` (`wcnf_spec`), by induction
         on the component list.

  §64.5  the fold: `stepF`/`idxOf`/`scanSt` copy `collapse`'s own fold, `collapse_eq` is
         `rfl`, and `fold_inv` carries the invariant "both accumulator slots are `inT` and
         below `M`" through it.  `inT_collapse`, `inT_dict` and `collapseInT_of_gaps` follow.

WHAT IS NOT PROVED, AND IS NOT WEAKENED AWAY.  Exactly three named hypotheses, and
`collapseInT_of_gaps` shows `CollapseInT` follows from them:

  (G1) `DivDescInT` — `divAP w` maps a descending list to a descending list, PROVIDED every
       member is `≥ w`.  **The side condition is not decoration: without it the statement is
       FALSE.**  Smallest counterexample found, `w = M`, `l = [M, Z0]` (degree sum 5):
       `divAP M M = 1` but `divAP M (Z0) = Z0`, so `[1, Z0]` is not descending.  With `w`
       restricted to R the smallest is `w = Z M`, `l = [Z M, Z 0]` (degree sum 7) — so
       "regular" does NOT rescue it and "every member `≥ w`" does: 0 failures on 82 373
       (w, l) pairs.  This is `Evidence/CNVOps.lean` §27–§29's `omegaNF_mono` one notch up
       (`CNV` → `inT`), and that is why it is not proved here: `DnFacts` is a theorem for
       `CNV` only, and its `inT` version is a section of its own.

  (G2) `MulDescInT` — the same for `mulL`'s map `p ↦ ω^(e ⊕ logOm p)`.  Here NO side
       condition was needed: 0 failures on 274 576 `inT` pairs.  Both (G1) and (G2) were
       re-measured on a SECOND, independently seeded population of 80 deeper terms
       (max degree 12): 0 failures on 2324 and 6400 pairs respectively.

  (G3) `PsiIdxOK u x` — [Rathjen, 1991] 2.1(vi)'s LAST conjunct, `K_κ α < α`, for the indices
       the strongly critical branch actually emits.  It is stated over `scanSt`, the list of
       (state, component) pairs the fold really visits, so it says nothing about indices the
       fold never builds.  **It is not vacuous and it is not free**: on a hand corpus of 463
       `inT` terms below `M` it FAILS 17 times at `u = 0`.  Smallest by degree, `x = ψ_{ZM}(ZM)`
       (degree 5): the whole of `x` is below `Ω = Z0`, so `wcnf` hands the fold one component
       with exponent `≥ Ω`, the emitted index is `x` itself, and `K_Ω x = {ZM}` — which is NOT
       `< x`, so `ψ_Ω x` is not a term.  On `dict`'s image — 1805 systematically enumerated
       `BT` terms, `BT.isStd` NOT applied — it holds for every one of them at `u = 0,1,2,3`.

  For the fragment where the strongly critical branch never fires, (G3) is discharged:
  `inT_collapse_noSC` needs only (G1) and (G2).  That fragment is 743 of the 1805 at `u = 0`,
  1804 of 1805 at `u = 1` and all of them at `u = 2`.

WHAT IS NOT CLAIMED.  `CollapseInT` is NOT discharged.  Nothing here says `dict`'s image is
characterised; (G3) is stated for a given `x` and MEASURED on `dict`'s image, not proved
there.  The order-theoretic content of (G1)/(G2) — monotonicity of `ω^·` on `inT` — and the
Kset content of (G3) are the two things a next attempt has to buy.

**CORRECTION (§65).  `DivDescInT` as stated here is FALSE** — `not_divDescInT` proves it,
smallest counterexample `w = ω`, `l = [ω^ω, ω]`.  So every theorem of this section that takes
it as a hypothesis (`wcnf_spec`, `inT_collapse`, `inT_collapse_noSC`, `inT_dict`,
`collapseInT_of_gaps`, `hsuccS_supply_of_gaps`) is VACUOUS and must not be used.  §65 restates
them against `DivDescSC`, which adds `w.isSC` and IS proved; the live consumers are
`collapseInT_of_gap3` and `hsuccS_supply_of_gap3`, whose only hypothesis is (G3).
-/


/-! ### §64.1 `M` の下 — `lt · M` は頭部だけで決まる

[Rathjen, 1991] 2.3.2 (`φ̄, ψ, Z < M`) と 2.3.3 (`M < ω̄^γ`) を、和の頭部を読むだけの判定
`hdBelowM` にまとめる。2.1(v) の 2 つの側条件はすべてここから出る。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- `M` より小さいか。和は頭部成分だけで決まる ([Rathjen, 1991] 2.3.2, 2.3.3, 2.3.10)。 -/
def hdBelowM : Term → Bool
  | M => false
  | omg _ => false
  | add a _ => hdBelowM a
  | _ => true

theorem inT_zero : inT (zero : Term) = true := rfl
theorem inT_M : inT (M : Term) = true := rfl

theorem lt_zero_M : lt zero M = true := by
  rw [Evidence.WF.lt_eq_ltF zero M ((zero : Term).deg + (M : Term).deg) (Nat.le_refl _)]; rfl

theorem lt_M_M : lt M M = false := by
  rw [Evidence.WF.lt_eq_ltF M M ((M : Term).deg + (M : Term).deg) (Nat.le_refl _)]; rfl

theorem lt_omg_M (a : Term) : lt (omg a) M = false := by
  rw [Evidence.WF.lt_eq_ltF (omg a) M ((omg a).deg + (M : Term).deg) (Nat.le_refl _)]
  show (if ((omg a) == M) = true then false else false) = false
  rw [show (((omg a) == M) : Bool) = false from rfl]; rfl

theorem lt_psi_M (k a : Term) : lt (psi k a) M = true := by
  rw [Evidence.WF.lt_eq_ltF (psi k a) M ((psi k a).deg + (M : Term).deg) (Nat.le_refl _)]
  show (if ((psi k a) == M) = true then false else true) = true
  rw [show (((psi k a) == M) : Bool) = false from rfl]; rfl

theorem lt_Z_M (a : Term) : lt (Z a) M = true := by
  rw [Evidence.WF.lt_eq_ltF (Z a) M ((Z a).deg + (M : Term).deg) (Nat.le_refl _)]
  show (if ((Z a) == M) = true then false else true) = true
  rw [show (((Z a) == M) : Bool) = false from rfl]; rfl

theorem lt_one_M : lt one M = true := lt_phi_M zero zero

/-- **`lt · M` は構造的。** -/
theorem lt_M_eq : ∀ (t : Term), lt t M = hdBelowM t
  | zero => lt_zero_M
  | M => lt_M_M
  | omg a => lt_omg_M a
  | phi a b => lt_phi_M a b
  | psi k a => lt_psi_M k a
  | Z a => lt_Z_M a
  | add a b => by rw [lt_add_M a b, lt_M_eq a]; rfl

theorem lt_ofList_M : ∀ (l : List Term), (∀ x ∈ l, lt x M = true) → lt (ofList l) M = true
  | [], _ => lt_zero_M
  | [a], h => h a (List.Mem.head _)
  | a :: b :: t, h => by
    show lt (add a (ofList (b :: t))) M = true
    rw [lt_add_M]
    exact h a (List.Mem.head _)

theorem lt_M_of_le {y a : Term} (hy : inT y = true) (ha : inT a = true)
    (hle : le y a = true) (hla : lt a M = true) : lt y M = true := by
  rcases (Bool.or_eq_true _ _).mp hle with h | h
  · rw [show y = a from eq_of_beq h]; exact hla
  · exact lt_trans_inT hy ha inT_M h hla

theorem ltM_of_hdLe : ∀ {a b : Term}, inT a = true → inT b = true →
    hdLe b a = true → lt a M = true → lt b M = true := by
  intro a b hia hib hhd hla
  cases b with
  | zero => exact Bool.noConfusion hhd
  | M => exact lt_M_of_le hib hia hhd hla
  | omg c => exact lt_M_of_le hib hia hhd hla
  | phi c d => exact lt_M_of_le hib hia hhd hla
  | psi c d => exact lt_M_of_le hib hia hhd hla
  | Z c => exact lt_M_of_le hib hia hhd hla
  | add c d =>
    obtain ⟨_, hic, _, _⟩ := inT_add hib
    rw [lt_add_M]
    exact lt_M_of_le hic hia hhd hla

/-- `M` より下の項の成分はすべて `M` より下。 -/
theorem ltM_toList : ∀ (s : Term), inT s = true → lt s M = true →
    ∀ x ∈ toList s, lt x M = true := by
  intro s
  induction s with
  | zero => intro _ _ x hx; cases hx
  | M => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | omg a _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | phi a b _ _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | psi k a _ _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | Z a _ => intro _ h x hx; rw [List.mem_singleton.mp hx]; exact h
  | add a b _ ihb =>
    intro h hl x hx
    obtain ⟨hap, hia, hib, hhd⟩ := inT_add h
    have hla : lt a M = true := by rw [← lt_add_M a b]; exact hl
    have hlb : lt b M = true := ltM_of_hdLe hia hib hhd hla
    rcases List.mem_cons.mp (show x ∈ a :: toList b from hx) with h1 | h1
    · rw [h1]; exact hla
    · exact ihb hib hlb x h1

theorem lt_plus_M {s t : Term} (hs : inT s = true) (ht : inT t = true)
    (hls : lt s M = true) (hlt : lt t M = true) : lt (plus s t) M = true := by
  cases hl : toList t with
  | nil => rw [show plus s t = s from by unfold TM.Term.plus; rw [hl]]; exact hls
  | cons b1 rest =>
    rw [plus_eq (s := s) hl]
    refine lt_ofList_M _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact ltM_toList s hs hls x (List.mem_filter.mp h1).1
    · exact ltM_toList t ht hlt x h1

end

/-! ### §64.2 演算ごとの `inT` 保存

`Trans/Dict.lean` の `collapse` が使う演算を 1 つずつ。どれも「`inT` を保つ」と
「`M` の下に留まる」を対にして出す。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (sub1 subAP logOm divAP)

theorem inT_ofNat : ∀ n, inT (ofNat n) = true
  | 0 => rfl
  | n + 1 => inT_plus (inT_ofNat n) inT_one

theorem ltM_ofNat : ∀ n, lt (ofNat n) M = true
  | 0 => lt_zero_M
  | n + 1 => lt_plus_M (inT_ofNat n) inT_one (ltM_ofNat n) lt_one_M

/-- 2.1(v) の 4 つの連言。 -/
theorem inT_phi4 {a b : Term} (h : inT (phi a b) = true) :
    inT a = true ∧ inT b = true ∧ lt a M = true ∧ lt b M = true := by
  have h' : (inT a && inT b && lt a M && lt b M) = true := h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h'
  obtain ⟨h3, h4⟩ := (Bool.and_eq_true _ _).mp h1
  obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
  exact ⟨h5, h6, h4, h2⟩

theorem inT_phi_intro {a b : Term} (hia : inT a = true) (hib : inT b = true)
    (hla : lt a M = true) (hlb : lt b M = true) : inT (phi a b) = true := by
  show (inT a && inT b && lt a M && lt b M) = true
  rw [hia, hib, hla, hlb]; rfl

theorem inT_phiNFdefault {a b : Term} (hia : inT a = true) (hib : inT b = true)
    (hla : lt a M = true) (hlb : lt b M = true) : inT (phiNFdefault a b) = true := by
  unfold phiNFdefault
  split
  · exact hia
  · exact inT_phi_intro hia hib hla hlb

theorem ltM_phiNFdefault {a b : Term} (hla : lt a M = true) :
    lt (phiNFdefault a b) M = true := by
  unfold phiNFdefault
  split
  · exact hla
  · exact lt_phi_M a b

theorem inT_take_ofList {b : Term} (h : inT b = true) (k : Nat) :
    inT (ofList ((toList b).take k)) = true := by
  obtain ⟨hc, hd⟩ := inT_toList b h
  exact inT_ofList _ (inTL_take k _ hc) (descL_take k _ hd)

theorem ltM_take_ofList {b : Term} (h : inT b = true) (hl : lt b M = true) (k : Nat) :
    lt (ofList ((toList b).take k)) M = true :=
  lt_ofList_M _ (fun x hx => ltM_toList b h hl x (List.mem_of_mem_take hx))

theorem inT_splitFin {b : Term} (h : inT b = true) : inT (splitFin b).1 = true :=
  inT_take_ofList h _

theorem ltM_splitFin {b : Term} (h : inT b = true) (hl : lt b M = true) :
    lt (splitFin b).1 M = true := ltM_take_ofList h hl _

theorem inT_phiNFsucc {a b : Term} (hia : inT a = true) (hib : inT b = true)
    (hla : lt a M = true) (hlb : lt b M = true) : inT (phiNFsucc a b) = true := by
  have hdef := inT_phiNFdefault hia hib hla hlb
  have hg : inT (splitFin b).1 = true := inT_splitFin hib
  have hgm : lt (splitFin b).1 M = true := ltM_splitFin hib hlb
  unfold phiNFsucc
  split
  rename_i heq
  rw [heq] at hg hgm
  split
  · split <;> (split <;>
      first
        | exact inT_phi_intro hia (inT_plus hg (inT_ofNat _)) hla
            (lt_plus_M hg (inT_ofNat _) hgm (ltM_ofNat _))
        | exact hdef)
  · exact hdef

theorem ltM_phiNFsucc {a b : Term} (hla : lt a M = true) :
    lt (phiNFsucc a b) M = true := by
  have hdef := ltM_phiNFdefault (b := b) hla
  unfold phiNFsucc
  split
  rename_i heq
  split
  · split <;> (split <;> first | exact lt_phi_M _ _ | exact hdef)
  · exact hdef

/-- **`φαβ` は 𝔗(M) に留まる** — 2.1(v) の 2 つの側条件つき。 -/
theorem inT_phiNF {a b : Term} (hia : inT a = true) (hib : inT b = true)
    (hla : lt a M = true) (hlb : lt b M = true) : inT (phiNF a b) = true := by
  unfold phiNF
  split
  · exact hib
  · split
    · split
      · exact hib
      · exact inT_phiNFsucc hia hib hla hlb
    · exact inT_phiNFsucc hia hib hla hlb

theorem ltM_phiNF {a b : Term} (hla : lt a M = true) (hlb : lt b M = true) :
    lt (phiNF a b) M = true := by
  unfold phiNF
  split
  · exact hlb
  · split
    · split
      · exact hlb
      · exact ltM_phiNFsucc hla
    · exact ltM_phiNFsucc hla

theorem ltM_of_not_gt {x : Term} (hx : inT x = true) (h1 : lt M x = false)
    (h2 : (x == M) = false) : lt x M = true := by
  rcases lt_trichotomy_inT hx inT_M with ⟨h, _, _⟩ | ⟨_, he, _⟩ | ⟨_, _, h⟩
  · exact h
  · exact absurd (beq_of_eq he) (by rw [h2]; exact Bool.noConfusion)
  · exact absurd h (by rw [h1]; exact Bool.noConfusion)

/-- **`ω^α` は 𝔗(M) に留まる** — 側条件なし。`ω̄^·` の枝は 2.1(iv) の `M < α` を自分で持つ。 -/
theorem inT_omegaNF {x : Term} (hx : inT x = true) : inT (omegaNF x) = true := by
  unfold omegaNF
  split
  · rename_i h
    show (inT x && lt M x) = true
    rw [hx, h]; rfl
  · split
    · exact inT_M
    · rename_i h1 h2
      exact inT_phiNF inT_zero hx lt_zero_M
        (ltM_of_not_gt hx (bool_false h1) (bool_false h2))

theorem ltM_omegaNF {x : Term} (hx : inT x = true) (hlx : lt x M = true) :
    lt (omegaNF x) M = true := by
  unfold omegaNF
  split
  · rename_i h
    exact absurd hlx (by rw [lt_asymm_inT inT_M hx h]; exact Bool.noConfusion)
  · split
    · rename_i h1 h2
      exact absurd hlx (by rw [eq_of_beq h2, lt_M_M]; exact Bool.noConfusion)
    · exact ltM_phiNF lt_zero_M hlx

/-- `sub1` と `subAP` は同じ形 — 先頭を落とすか、そのまま返すか。 -/
theorem inT_dropIfHead {c : Term} (h : inT c = true) (P : Term → Bool) :
    inT (match toList c with
         | [] => zero
         | p :: rest => if P p then ofList rest else c) = true := by
  cases hl : toList c with
  | nil => exact inT_zero
  | cons p rest =>
    obtain ⟨hc, hd⟩ := inT_toList c h
    rw [hl] at hc hd
    show inT (if P p = true then ofList rest else c) = true
    split
    · exact inT_ofList rest (inTL_cons.mp hc).2 (descL_tail hd)
    · exact h

theorem ltM_dropIfHead {c : Term} (h : inT c = true) (hlc : lt c M = true) (P : Term → Bool) :
    lt (match toList c with
        | [] => zero
        | p :: rest => if P p then ofList rest else c) M = true := by
  cases hl : toList c with
  | nil => exact lt_zero_M
  | cons p rest =>
    show lt (if P p = true then ofList rest else c) M = true
    split
    · exact lt_ofList_M rest (fun x hx =>
        ltM_toList c h hlc x (by rw [hl]; exact List.Mem.tail p hx))
    · exact hlc

theorem inT_sub1 {c : Term} (h : inT c = true) : inT (sub1 c) = true :=
  inT_dropIfHead h (fun p => p == one)

theorem ltM_sub1 {c : Term} (h : inT c = true) (hl : lt c M = true) :
    lt (sub1 c) M = true := ltM_dropIfHead h hl (fun p => p == one)

theorem inT_subAP {w x : Term} (h : inT x = true) : inT (subAP w x) = true :=
  inT_dropIfHead h (fun p => p == w)

theorem ltM_subAP {w x : Term} (h : inT x = true) (hl : lt x M = true) :
    lt (subAP w x) M = true := ltM_dropIfHead h hl (fun p => p == w)

theorem inT_logOm {t : Term} (ht : inT t = true) : inT (logOm t) = true := by
  cases t with
  | zero => exact ht
  | M => exact ht
  | omg a => exact ht
  | psi k a => exact ht
  | Z a => exact ht
  | add a b => exact ht
  | phi c d =>
    cases c with
    | zero =>
      obtain ⟨_, hd, _, _⟩ := inT_phi4 ht
      show inT (if TM.Term.phiShifted zero d then plus d one else d) = true
      split
      · exact inT_plus hd inT_one
      · exact hd
    | M => exact ht
    | omg _ => exact ht
    | phi _ _ => exact ht
    | psi _ _ => exact ht
    | Z _ => exact ht
    | add _ _ => exact ht

theorem ltM_logOm {t : Term} (ht : inT t = true) (hl : lt t M = true) :
    lt (logOm t) M = true := by
  cases t with
  | zero => exact hl
  | M => exact hl
  | omg a => exact hl
  | psi k a => exact hl
  | Z a => exact hl
  | add a b => exact hl
  | phi c d =>
    cases c with
    | zero =>
      obtain ⟨_, hd, _, hld⟩ := inT_phi4 ht
      show lt (if TM.Term.phiShifted zero d then plus d one else d) M = true
      split
      · exact lt_plus_M hd inT_one hld lt_one_M
      · exact hld
    | M => exact hl
    | omg _ => exact hl
    | phi _ _ => exact hl
    | psi _ _ => exact hl
    | Z _ => exact hl
    | add _ _ => exact hl

theorem inT_divAP {w p : Term} (hp : inT p = true) : inT (divAP w p) = true :=
  inT_omegaNF (inT_subAP (inT_logOm hp))

theorem ltM_divAP {w p : Term} (hp : inT p = true) (hlp : lt p M = true) :
    lt (divAP w p) M = true :=
  ltM_omegaNF (inT_subAP (inT_logOm hp)) (ltM_subAP (inT_logOm hp) (ltM_logOm hp hlp))

theorem isAP_divAP (w p : Term) : (divAP w p).isAP = true := isAP_omegaNF _

end

/-! ### §64.3 成分列の道具、そして単調性の 2 つの穴

`ofList` が 𝔗(M) の項になるには成分が降順でなければならない (2.1(iii))。`filter` は
`le_trans_inT` を 1 度だけ使えば降順を保つ。`map` はそうはいかない — そこが穴で、
`DivDescInT` と `MulDescInT` に名前をつけて分離する。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (logOm divAP mulL)

/-- 降順の列は頭で押さえられる。`le_trans_inT` を使うのはここだけ。 -/
theorem descL_bound_inT : ∀ (l : List Term) (a : Term), inT a = true → inTL l = true →
    descL (a :: l) = true → ∀ x ∈ l, le x a = true := by
  intro l
  induction l with
  | nil => intro _ _ _ _ x hx; cases hx
  | cons b t ih =>
    intro a hia hc hd x hx
    obtain ⟨hba, hdt⟩ := descL_cons.mp hd
    obtain ⟨⟨_, hib⟩, hct⟩ := inTL_cons.mp hc
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact hba
    · have hxb : le x b = true := ih b hib hct hdt x h
      have hix : inT x = true := ((Bool.and_eq_true _ _).mp
        (List.all_eq_true.mp hct x h)).2
      exact le_trans_inT hix hib hia hxb hba

theorem inTL_filter (P : Term → Bool) : ∀ {l : List Term}, inTL l = true →
    inTL (l.filter P) = true := by
  intro l h
  show (l.filter P).all _ = true
  rw [List.all_eq_true]
  intro x hx
  exact List.all_eq_true.mp h x (List.mem_filter.mp hx).1

theorem descL_filter_inT : ∀ (l : List Term), inTL l = true → descL l = true →
    ∀ (P : Term → Bool), descL (l.filter P) = true := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons a t ih =>
    intro hc hd P
    obtain ⟨⟨_, hia⟩, hct⟩ := inTL_cons.mp hc
    have hdt := descL_tail hd
    have hbound := descL_bound_inT t a hia hct hd
    by_cases hp : P a = true
    · rw [List.filter_cons_of_pos hp]
      cases hf : t.filter P with
      | nil => rfl
      | cons b s =>
        refine descL_cons.mpr ⟨?_, by rw [← hf]; exact ih hct hdt P⟩
        have hb : b ∈ t.filter P := by rw [hf]; exact List.Mem.head _
        exact hbound b (List.mem_filter.mp hb).1
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      exact ih hct hdt P

theorem inT_filter_ofList {l : List Term} (hc : inTL l = true) (hd : descL l = true)
    (P : Term → Bool) : inT (ofList (l.filter P)) = true :=
  inT_ofList _ (inTL_filter P hc) (descL_filter_inT l hc hd P)

theorem ltM_filter_ofList {l : List Term} (hm : ∀ x ∈ l, lt x M = true)
    (P : Term → Bool) : lt (ofList (l.filter P)) M = true :=
  lt_ofList_M _ (fun x hx => hm x (List.mem_filter.mp hx).1)

/-- **(G1) 穴 1。** `divAP w` は降順を保つ — **ただし列の成分がすべて `w` 以上のとき**。
    側条件を落とすと偽で、最小の反例は `w = M`, `l = [M, Z0]` (下の `#guard`)。
    `Evidence/CNVOps.lean` §27–§29 の `omegaNF_mono` の `inT` 版にあたる。 -/
def DivDescInT : Prop := ∀ (w : Term) (l : List Term), inT w = true →
  inTL l = true → descL l = true → (∀ q ∈ l, lt q w = false) →
  descL (l.map (divAP w)) = true

/-- **(G2) 穴 2。** `mulL` の写像も降順を保つ。側条件は測定では要らなかった。 -/
def MulDescInT : Prop := ∀ (e y : Term), inT e = true → inT y = true →
  descL ((toList y).map (fun p => omegaNF (plus e (logOm p)))) = true

theorem inT_mulL (H : MulDescInT) {e y : Term} (he : inT e = true) (hy : inT y = true) :
    inT (mulL e y) = true := by
  show inT (ofList ((toList y).map (fun p => omegaNF (plus e (logOm p))))) = true
  refine inT_ofList _ ?_ (H e y he hy)
  show ((toList y).map _).all _ = true
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨p, hp, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  show ((omegaNF (plus e (logOm p))).isAP && inT (omegaNF (plus e (logOm p)))) = true
  rw [isAP_omegaNF, inT_omegaNF (inT_plus he (inT_logOm (inTL_inT hy p hp)))]
  rfl

theorem ltM_mulL {e y : Term} (he : inT e = true) (hy : inT y = true)
    (hle : lt e M = true) (hly : lt y M = true) : lt (mulL e y) M = true := by
  show lt (ofList ((toList y).map (fun p => omegaNF (plus e (logOm p))))) M = true
  refine lt_ofList_M _ ?_
  intro x hx
  obtain ⟨p, hp, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  have hip := inTL_inT hy p hp
  have hlp := ltM_toList y hy hly p hp
  exact ltM_omegaNF (inT_plus he (inT_logOm hip))
    (lt_plus_M he (inT_logOm hip) hle (ltM_logOm hip hlp))

end

/-! ### §64.4 `wcnf` の成分

底 `w` の Cantor 標準形。指数 `a` と係数 `c` がどちらも 𝔗(M) の項で `M` の下にあること、
尾 `ρ` も同じであることを、成分列の帰納で出す。指数の側だけが (G1) を消費する。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (wcnf divAP logOm)

theorem wcnf_nil (w : Term) : wcnf w [] = ([], zero) := rfl

theorem wcnf_cons_lt {w p : Term} {rest : List Term} (h : lt p w = true) :
    wcnf w (p :: rest) = ([], ofList (p :: rest)) := by
  show (if lt p w = true then _ else _) = _
  rw [if_pos h]

/-- `wcnf` の 1 成分ぶんの指数。 -/
def wA (w p : Term) : Term :=
  ofList (((toList (logOm p)).filter (fun q => !lt q w)).map (divAP w))
/-- `wcnf` の 1 成分ぶんの係数。 -/
def wC (w p : Term) : Term :=
  omegaNF (ofList ((toList (logOm p)).filter (fun q => lt q w)))

theorem wcnf_cons_ge {w p : Term} {rest : List Term} (h : lt p w = false) :
    wcnf w (p :: rest) =
      (match wcnf w rest with
       | ((a', c') :: ps, tl) =>
         if wA w p == a' then ((wA w p, plus (wC w p) c') :: ps, tl)
         else ((wA w p, wC w p) :: (a', c') :: ps, tl)
       | ([], tl) => ([(wA w p, wC w p)], tl)) := by
  show (if lt p w = true then _ else _) = _
  rw [if_neg (by rw [h]; exact Bool.noConfusion)]
  rfl

theorem inT_wA (Hd : DivDescInT) {w p : Term} (hw : inT w = true) (hp : inT p = true) :
    inT (wA w p) = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  refine inT_ofList _ ?_
    (Hd w _ hw (inTL_filter _ hc) (descL_filter_inT _ hc hd _) ?_)
  · show (List.map (divAP w) _).all _ = true
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨q, hq, hxe⟩ := List.mem_map.mp hx
    rw [← hxe]
    show ((divAP w q).isAP && inT (divAP w q)) = true
    rw [isAP_divAP, inT_divAP (inTL_inT (inT_logOm hp) q (List.mem_filter.mp hq).1)]
    rfl
  · intro q hq
    have := (List.mem_filter.mp hq).2
    cases hlq : lt q w with
    | false => rfl
    | true => rw [hlq] at this; exact Bool.noConfusion this

theorem ltM_wA {w p : Term} (hp : inT p = true) (hlp : lt p M = true) :
    lt (wA w p) M = true := by
  refine lt_ofList_M _ ?_
  intro x hx
  obtain ⟨q, hq, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  have hmq := (List.mem_filter.mp hq).1
  exact ltM_divAP (inTL_inT (inT_logOm hp) q hmq)
    (ltM_toList _ (inT_logOm hp) (ltM_logOm hp hlp) q hmq)

theorem inT_wC {w p : Term} (hp : inT p = true) : inT (wC w p) = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  exact inT_omegaNF (inT_filter_ofList hc hd _)

theorem ltM_wC {w p : Term} (hp : inT p = true) (hlp : lt p M = true) :
    lt (wC w p) M = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  exact ltM_omegaNF (inT_filter_ofList hc hd _)
    (ltM_filter_ofList (ltM_toList _ (inT_logOm hp) (ltM_logOm hp hlp)) _)

/-- `wcnf` の返り値がすべて 𝔗(M) の項で `M` の下にあること。 -/
def PairOK (r : List (Term × Term) × Term) : Prop :=
  (inT r.2 = true ∧ lt r.2 M = true) ∧
  (∀ ac ∈ r.1, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true)

/-- **`wcnf` は 𝔗(M) の中に留まる。** (G1) だけを使う。 -/
theorem wcnf_spec (Hd : DivDescInT) {w : Term} (hw : inT w = true) : ∀ (L : List Term),
    inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) → PairOK (wcnf w L) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _
    exact ⟨⟨inT_zero, lt_zero_M⟩, by intro ac hac; cases hac⟩
  | cons p rest ih =>
    intro hc hd hm
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have hlpM : lt p M = true := hm p (List.Mem.head _)
    have IH := ih hcr hdr hmr
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp]
      exact ⟨⟨inT_ofList _ hc hd, lt_ofList_M _ hm⟩, by intro ac hac; cases hac⟩
    · have hlp' : lt p w = false := bool_false hlp
      have hA := inT_wA Hd (w := w) hw hip
      have hAM := ltM_wA (w := w) hip hlpM
      have hC := inT_wC (w := w) hip
      have hCM := ltM_wC (w := w) hip hlpM
      rw [wcnf_cons_ge hlp']
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at IH
        obtain ⟨⟨hs1, hs2⟩, hall⟩ := IH
        cases fst with
        | nil =>
          refine ⟨⟨hs1, hs2⟩, ?_⟩
          intro ac hac
          rw [List.mem_singleton.mp hac]
          exact ⟨hA, hAM, hC, hCM⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac0 := hall (a', c') (List.Mem.head _)
            show PairOK (if (wA w p == a') = true
              then ((wA w p, plus (wC w p) c') :: ps, snd)
              else ((wA w p, wC w p) :: (a', c') :: ps, snd))
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq]
              refine ⟨⟨hs1, hs2⟩, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]
                exact ⟨hA, hAM, inT_plus hC hac0.2.2.1,
                  lt_plus_M hC hac0.2.2.1 hCM hac0.2.2.2⟩
              · exact hall ac (List.Mem.tail _ h)
            · rw [if_neg heq]
              refine ⟨⟨hs1, hs2⟩, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with h | h
              · rw [h]; exact ⟨hA, hAM, hC, hCM⟩
              · exact hall ac h

end

/-! ### §64.5 畳み込み、`collapse`、そして `CollapseInT` が何に還元されるか

`stepF`・`idxOf`・`scanSt` は `collapse` の畳み込みをそのまま写したもので、`collapse_eq`
は `rfl`。不変量は「累算器の 2 つの枠がどちらも 𝔗(M) の項で `M` の下」。ヴェブレン枝は
§64.2 だけで閉じ、強臨界枝は `PsiIdxOK` — 2.1(vi) の最後の連言 — を消費する。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)

/-- 強臨界枝が組み立てる指数。`collapse` の定義をそのまま写したもの。 -/
def idxOf (w : Term) (s : Option Term × Option Term) (ac : Term × Term) : Term :=
  match s.1 with
  | none => sub1 (mulL (mulL w (subAP w ac.1)) ac.2)
  | some i0 => plus i0 (mulL (mulL w (subAP w ac.1)) ac.2)

/-- `collapse` の畳み込みの 1 歩。 -/
def stepF (w base : Term) (s : Option Term × Option Term) (ac : Term × Term) :
    Option Term × Option Term :=
  if le w ac.1 then (some (idxOf w s ac), some (psi w (idxOf w s ac)))
  else
    let bse := match s.2 with | none => base | some v => v
    let cc := match s.2 with | none => sub1 ac.2 | some _ => ac.2
    (s.1, some (phiNF ac.1 (plus bse cc)))

def baseOf (u : Nat) : Term := if u == 0 then zero else plus (reg u) TM.Term.one

/-- **`collapse` は畳み込みそのもの。** -/
theorem collapse_eq (u : Nat) (x : Term) :
    collapse u x =
      omegaNF (plus (reg u) (plus
        (((wcnf (reg (u+1)) (toList x)).1.foldl
            (init := ((none : Option Term), (none : Option Term)))
            (stepF (reg (u+1)) (baseOf u))).2.getD zero)
        (wcnf (reg (u+1)) (toList x)).2)) := rfl

/-- 畳み込みが実際に通る (状態, 成分) の並び。 -/
def scanSt (w base : Term) : (Option Term × Option Term) → List (Term × Term) →
    List ((Option Term × Option Term) × (Term × Term))
  | _, [] => []
  | s, ac :: t => (s, ac) :: scanSt w base (stepF w base s ac) t

theorem scanSt_mem_snd : ∀ (w base : Term) (s : Option Term × Option Term)
    (l : List (Term × Term)) (p : (Option Term × Option Term) × (Term × Term)),
    p ∈ scanSt w base s l → p.2 ∈ l := by
  intro w base s l
  induction l generalizing s with
  | nil => intro p hp; cases hp
  | cons ac t ih =>
    intro p hp
    rcases List.mem_cons.mp (show p ∈ (s, ac) :: scanSt w base (stepF w base s ac) t from hp)
      with h | h
    · rw [h]; exact List.Mem.head _
    · exact List.Mem.tail _ (ih (stepF w base s ac) p h)

theorem inT_reg : ∀ u, inT (reg u) = true
  | 0 => inT_zero
  | u + 1 => show inT (ofNat u) = true from inT_ofNat u

theorem ltM_reg : ∀ u, lt (reg u) M = true
  | 0 => lt_zero_M
  | _ + 1 => lt_Z_M _

theorem inT_baseOf (u : Nat) : inT (baseOf u) = true := by
  unfold baseOf
  split
  · exact inT_zero
  · exact inT_plus (inT_reg u) inT_one

theorem ltM_baseOf (u : Nat) : lt (baseOf u) M = true := by
  unfold baseOf
  split
  · exact lt_zero_M
  · exact lt_plus_M (inT_reg u) inT_one (ltM_reg u) lt_one_M

/-- 畳み込みの不変量。 -/
def StInv (s : Option Term × Option Term) : Prop :=
  (∀ i0, s.1 = some i0 → inT i0 = true ∧ lt i0 M = true) ∧
  (∀ v, s.2 = some v → inT v = true ∧ lt v M = true)

theorem inT_idxOf (Hm : MulDescInT) {w : Term} (hw : inT w = true) (hlw : lt w M = true)
    {s : Option Term × Option Term} {ac : Term × Term} (hs : StInv s)
    (h1 : inT ac.1 = true) (h2 : lt ac.1 M = true) (h3 : inT ac.2 = true)
    (h4 : lt ac.2 M = true) :
    inT (idxOf w s ac) = true ∧ lt (idxOf w s ac) M = true := by
  have he : inT (mulL w (subAP w ac.1)) = true := inT_mulL Hm hw (inT_subAP h1)
  have hle : lt (mulL w (subAP w ac.1)) M = true :=
    ltM_mulL hw (inT_subAP h1) hlw (ltM_subAP h1 h2)
  have hd : inT (mulL (mulL w (subAP w ac.1)) ac.2) = true := inT_mulL Hm he h3
  have hld : lt (mulL (mulL w (subAP w ac.1)) ac.2) M = true := ltM_mulL he h3 hle h4
  unfold idxOf
  cases hs1 : s.1 with
  | none => exact ⟨inT_sub1 hd, ltM_sub1 hd hld⟩
  | some i0 =>
    obtain ⟨hi, hli⟩ := hs.1 i0 hs1
    exact ⟨inT_plus hi hd, lt_plus_M hi hd hli hld⟩

theorem stepF_inv (Hm : MulDescInT) {w base : Term} (hw : inT w = true) (hlw : lt w M = true)
    (hb : inT base = true) (hlb : lt base M = true)
    {s : Option Term × Option Term} {ac : Term × Term} (hs : StInv s)
    (hac : inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true)
    (hpsi : le w ac.1 = true → inT (psi w (idxOf w s ac)) = true) :
    StInv (stepF w base s ac) := by
  obtain ⟨h1, h2, h3, h4⟩ := hac
  unfold stepF
  split
  · rename_i hle
    obtain ⟨hi, hli⟩ := inT_idxOf Hm hw hlw hs h1 h2 h3 h4
    refine ⟨?_, ?_⟩
    · intro i0 hq
      rw [← Option.some.inj (show some (idxOf w s ac) = some i0 from hq)]
      exact ⟨hi, hli⟩
    · intro v hq
      rw [← Option.some.inj (show some (psi w (idxOf w s ac)) = some v from hq)]
      exact ⟨hpsi hle, lt_psi_M _ _⟩
  · refine ⟨hs.1, ?_⟩
    intro v hq
    have hbse : inT (match s.2 with | none => base | some v => v) = true ∧
        lt (match s.2 with | none => base | some v => v) M = true := by
      cases hq2 : s.2 with
      | none => exact ⟨hb, hlb⟩
      | some v0 => exact hs.2 v0 hq2
    have hcc : inT (match s.2 with | none => sub1 ac.2 | some _ => ac.2) = true ∧
        lt (match s.2 with | none => sub1 ac.2 | some _ => ac.2) M = true := by
      cases hq2 : s.2 with
      | none => exact ⟨inT_sub1 h3, ltM_sub1 h3 h4⟩
      | some v0 => exact ⟨h3, h4⟩
    rw [← Option.some.inj (show some (phiNF ac.1
      (plus (match s.2 with | none => base | some v => v)
            (match s.2 with | none => sub1 ac.2 | some _ => ac.2))) = some v from hq)]
    exact ⟨inT_phiNF h1 (inT_plus hbse.1 hcc.1) h2
             (lt_plus_M hbse.1 hcc.1 hbse.2 hcc.2),
           ltM_phiNF h2 (lt_plus_M hbse.1 hcc.1 hbse.2 hcc.2)⟩

theorem fold_inv (Hm : MulDescInT) {w base : Term} (hw : inT w = true) (hlw : lt w M = true)
    (hb : inT base = true) (hlb : lt base M = true) :
    ∀ (l : List (Term × Term)) (s : Option Term × Option Term), StInv s →
      (∀ ac ∈ l, inT ac.1 = true ∧ lt ac.1 M = true ∧ inT ac.2 = true ∧ lt ac.2 M = true) →
      (∀ p ∈ scanSt w base s l, le w p.2.1 = true →
          inT (psi w (idxOf w p.1 p.2)) = true) →
      StInv (l.foldl (stepF w base) s) := by
  intro l
  induction l with
  | nil => intro s hs _ _; exact hs
  | cons ac t ih =>
    intro s hs hall hpsi
    have h1 : StInv (stepF w base s ac) :=
      stepF_inv Hm hw hlw hb hlb hs (hall ac (List.Mem.head _))
        (hpsi (s, ac) (List.Mem.head _))
    exact ih (stepF w base s ac) h1 (fun a ha => hall a (List.Mem.tail _ ha))
      (fun p hp => hpsi p (List.Mem.tail _ hp))

/-- **(G3) 穴 3。** 強臨界枝が実際に吐く指数について [Rathjen, 1991] 2.1(vi) の最後の連言。
    `scanSt` を通しているので、畳み込みが決して作らない指数については何も言っていない。
    一般には**偽** (下の `#guard`)。`dict` の像では 1805 項すべてで成り立つ (測定)。 -/
def PsiIdxOK (u : Nat) (x : Term) : Prop :=
  ∀ p ∈ scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1,
    le (reg (u+1)) p.2.1 = true →
    inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2)) = true

/-- **§64 の主定理。** `collapse` は 𝔗(M) に落ちる — (G1)(G2)(G3) を仮定して。 -/
theorem inT_collapse (Hd : DivDescInT) (Hm : MulDescInT) (u : Nat) (x : Term)
    (hx : inT x = true) (hlx : lt x M = true) (Hp : PsiIdxOK u x) :
    inT (collapse u x) = true ∧ lt (collapse u x) M = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨⟨h21, h22⟩, hallOK⟩ :=
    wcnf_spec Hd (inT_reg (u+1)) (toList x) hc hd (ltM_toList x hx hlx)
  have hinit : StInv ((none : Option Term), (none : Option Term)) := by
    constructor
    · intro i0 h; cases h
    · intro v h; cases h
  have hst := fold_inv Hm (inT_reg (u+1)) (ltM_reg (u+1)) (inT_baseOf u) (ltM_baseOf u)
    (wcnf (reg (u+1)) (toList x)).1 (none, none) hinit hallOK Hp
  have hv : inT (((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2.getD zero) = true ∧
      lt (((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2.getD zero) M = true := by
    cases hg : ((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2 with
    | none => exact ⟨inT_zero, lt_zero_M⟩
    | some v => exact hst.2 v hg
  rw [collapse_eq]
  have harg : inT (plus (reg u) (plus _ (wcnf (reg (u+1)) (toList x)).2)) = true :=
    inT_plus (inT_reg u) (inT_plus hv.1 h21)
  have hlarg : lt (plus (reg u) (plus _ (wcnf (reg (u+1)) (toList x)).2)) M = true :=
    lt_plus_M (inT_reg u) (inT_plus hv.1 h21) (ltM_reg u)
      (lt_plus_M hv.1 h21 hv.2 h22)
  exact ⟨inT_omegaNF harg, ltM_omegaNF harg hlarg⟩

/-- 強臨界枝が一度も点火しないなら (G3) は自動的に成り立つ。 -/
theorem psiIdxOK_of_noSC (u : Nat) (x : Term)
    (h : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = false) :
    PsiIdxOK u x := by
  intro p hp hle
  have hmem := scanSt_mem_snd _ _ _ _ p hp
  exact absurd hle (by rw [h p.2 hmem]; exact Bool.noConfusion)

/-- **強臨界枝のない断片では (G3) は要らない。** -/
theorem inT_collapse_noSC (Hd : DivDescInT) (Hm : MulDescInT) (u : Nat) (x : Term)
    (hx : inT x = true) (hlx : lt x M = true)
    (h : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = false) :
    inT (collapse u x) = true :=
  (inT_collapse Hd Hm u x hx hlx (psiIdxOK_of_noSC u x h)).1

/-- `dict` の像は 𝔗(M) の中で `M` の下にある — 3 つの穴を仮定して。 -/
theorem inT_dict (Hd : DivDescInT) (Hm : MulDescInT)
    (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :
    ∀ a : BT, inT (dict a) = true ∧ lt (dict a) M = true
  | .zero => ⟨inT_zero, lt_zero_M⟩
  | .D u a => by
    have ih := inT_dict Hd Hm Hp a
    exact inT_collapse Hd Hm u (dict a) ih.1 ih.2 (Hp u a)
  | .sum a b => by
    have iha := inT_dict Hd Hm Hp a
    have ihb := inT_dict Hd Hm Hp b
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- **§63 の `CollapseInT` は、名前のついた 3 つの事実に還元される。** -/
theorem collapseInT_of_gaps (Hd : DivDescInT) (Hm : MulDescInT)
    (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) : CollapseInT :=
  fun u a => (inT_dict Hd Hm Hp (BT.D u a)).1

/-- **消費者を通す。** §63 の `hsuccS_supply` — `certIn_region` の 2 番目の供給 — が
    (G1)(G2)(G3) だけで開く。仮説が満たせないものでないことの確認はこれ。 -/
theorem hsuccS_supply_of_gaps (Hd : DivDescInT) (Hm : MulDescInT)
    (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS (BMS.expand S n) u :=
  hsuccS_supply (collapseInT_of_gaps Hd Hm Hp)

end

/-! ### §64.6 測定 (凍結)

否定的なものから。 -/

section
open TM TM.Term
open Evidence.WF
open Trans.Recal
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)

/-- 測定用の判定器。 -/
def divDescb (w : Term) (l : List Term) : Bool := descL (l.map (divAP w))
def mulDescb (e y : Term) : Bool := descL ((toList y).map (fun p => omegaNF (plus e (logOm p))))
def psiIdxOKb (u : Nat) (x : Term) : Bool :=
  (scanSt (reg (u+1)) (baseOf u) (none, none) (wcnf (reg (u+1)) (toList x)).1).all
    fun p => !(le (reg (u+1)) p.2.1) || inT (psi (reg (u+1)) (idxOf (reg (u+1)) p.1 p.2))
def noSCb (u : Nat) (x : Term) : Bool :=
  (wcnf (reg (u+1)) (toList x)).1.all fun ac => !(le (reg (u+1)) ac.1)

-- **否定 1.** `inT x` だけでは `inT (collapse u x)` は出ない。最小は `x = M`。
#guard inT (M : Term)
#guard !(inT (Trans.Dict.collapse 0 M))

-- **否定 2.** `inT x && lt x M` でも出ない。最小は `x = ψ_{ZM}(ZM)` (次数 5)。
#guard inT (psi (Z M) (Z M)) && lt (psi (Z M) (Z M)) M
#guard (psi (Z M) (Z M)).deg == 5
#guard !(inT (Trans.Dict.collapse 0 (psi (Z M) (Z M))))
--   落ちるのはちょうど (G3) — 吐かれる指数は `x` 自身で、`K_Ω x = {ZM}` が `x` 未満でない。
#guard !(psiIdxOKb 0 (psi (Z M) (Z M)))
#guard Kset (Z zero) (psi (Z M) (Z M)) == [Z M]
#guard !(lt (Z M) (psi (Z M) (Z M)))
--   次数 10 の `φ̄(Ω, ψ_Ω(Z1))` も同じ形で落ちる (機構は同一)。
#guard !(psiIdxOKb 0 (phi (Z zero) (psi (Z zero) (Z one))))

-- **否定 3.** (G1) の側条件を落とすと偽。最小は `w = M`, `l = [M, Z0]` (次数和 5)。
#guard inT (add M (Z zero)) && descL (TM.Term.toList (add M (Z zero)))
#guard !(divDescb M (TM.Term.toList (add M (Z zero))))
#guard ((TM.Term.toList (add M (Z zero))).map (divAP M)) == [one, Z zero]
--   `w` を R に限っても救われない。最小は `w = Z M`, `l = [Z M, Z 0]` (次数和 7)。
#guard (Z M).isR && inT (add (Z M) (Z zero))
#guard !(divDescb (Z M) (TM.Term.toList (add (Z M) (Z zero))))
--   救うのは「成分がすべて `w` 以上」。上の 2 つはどちらもそれを破る。
#guard !((TM.Term.toList (add M (Z zero))).all (fun q => !lt q M))
#guard !((TM.Term.toList (add (Z M) (Z zero))).all (fun q => !lt q (Z M)))

/-! 肯定。母集団は 2 つ — 手作りの `inT` 項 (`corp64`) と `dict` の像 (`bcorp64`)。 -/

private def at64 : List Term :=
  [zero, one, omega, phi one zero, Z zero, Z one, psi (Z zero) zero,
   psi (Z zero) (Z one), M, omg (add M one), psi M M, phi M M, Z (Z zero), Z M,
   psi (Z one) zero, psi (Z one) (Z zero), phi (Z zero) zero, phi zero (Z zero)]
private def corp64 : List Term :=
  at64
  ++ (at64.flatMap fun a => at64.map fun b => add a b)
  ++ (at64.flatMap fun a => at64.map fun b => phi a b)
  ++ (at64.flatMap fun a => at64.map fun b => psi a b)
  ++ (at64.map fun a => omg a)
  ++ (at64.map fun a => Z a)
  ++ (at64.flatMap fun a => at64.map fun b => add a (add b one))
private def gT64 : List Term := corp64.filter fun x => inT x
private def gTM64 : List Term := corp64.filter fun x => inT x && lt x M
private def bseed64 : List BT := [.zero, .D 0 .zero, .D 1 .zero, .D 2 .zero, .D 0 (.D 1 .zero)]
private def bstep64 (l : List BT) : List BT :=
  l ++ (List.range 3).flatMap (fun u => l.map (fun a => BT.D u a))
    ++ (l.flatMap fun a => l.map fun b => BT.sum a b)
private def bcorp64 : List BT := (bstep64 (bstep64 bseed64).eraseDups).eraseDups

#guard corp64.length == 1350
#guard gT64.length == 524
#guard gTM64.length == 463
#guard bcorp64.length == 1805

-- 肯定 1.  (G1) — 側条件つきなら 0 失敗。`gT64` の全ペアで 82 373 組。
#guard (gT64.flatMap fun w => gT64.filter fun y =>
    (TM.Term.toList y).all (fun q => !lt q w) && !(divDescb w (TM.Term.toList y))).length == 0
#guard (gT64.flatMap fun w => gT64.filter fun y =>
    (TM.Term.toList y).all (fun q => !lt q w)).length == 82373

-- 肯定 2.  (G2) — 側条件なしで 0 失敗。`gT64` の全ペアで 274 576 組。
#guard (gT64.flatMap fun e => gT64.filter fun y => !(mulDescb e y)).length == 0
#guard gT64.length * gT64.length == 274576

-- 肯定 3.  (G3) — `dict` の像 1805 項すべて、`u = 0,1,2,3` で 0 失敗。
--   **`BT.isStd` で絞っていない。**
#guard (bcorp64.filter fun a => !(psiIdxOKb 0 (dict a))).length == 0
#guard (bcorp64.filter fun a => !(psiIdxOKb 1 (dict a))).length == 0
#guard (bcorp64.filter fun a => !(psiIdxOKb 2 (dict a))).length == 0
#guard (bcorp64.filter fun a => !(psiIdxOKb 3 (dict a))).length == 0
#guard !(bcorp64.all fun a => BT.isStd a)
--   そして (G3) は真空ではない。手作りの母集団では `u = 0` で 17 回落ちる。
#guard (gTM64.filter fun x => !(psiIdxOKb 0 x)).length == 17
#guard (gTM64.filter fun x => !(psiIdxOKb 1 x)).length == 3

-- 肯定 4.  `inT_collapse_noSC` の射程。`u = 0` で 743/1805、`u = 1` で 1804/1805。
#guard (bcorp64.filter fun a => noSCb 0 (dict a)).length == 743
#guard (bcorp64.filter fun a => noSCb 1 (dict a)).length == 1804
#guard (bcorp64.filter fun a => noSCb 2 (dict a)).length == 1805

-- 肯定 5.  `dict` の像は `inT` かつ `M` の下 — §64.5 の `inT_dict` が結論する形。
#guard bcorp64.all fun a => inT (dict a) && lt (dict a) M

-- 肯定 7.  (G1)(G2) の第 2 母集団 — 種を変えて 2 回閉じた深い項 (最大次数 12)。
--   種は {0, 1, Ω, M, ψ_Ω0, ω^Ω}、閉包は add/phi/psi/Z/omg。
private def a64 : List Term := [zero, one, Z zero, M, psi (Z zero) zero, phi zero (Z zero)]
private def step64 (l : List Term) : List Term :=
  l ++ (l.flatMap fun a => l.map fun b => add a b)
    ++ (l.flatMap fun a => l.map fun b => phi a b)
    ++ (l.flatMap fun a => l.map fun b => psi a b)
    ++ (l.map fun a => Z a) ++ (l.map fun a => omg a)
private def a64' : List Term := (step64 a64).eraseDups.filter fun x => inT x
private def deep64 : List Term :=
  (((step64 (a64'.take 14)).eraseDups).filter fun x => inT x).take 80
#guard a64'.length == 53
#guard deep64.length == 80
#guard (deep64.map fun x => x.deg).foldl (fun a b => if a < b then b else a) 0 == 12
#guard (deep64.flatMap fun w => deep64.filter fun y =>
    (TM.Term.toList y).all (fun q => !lt q w) && !(divDescb w (TM.Term.toList y))).length == 0
#guard (deep64.flatMap fun w => deep64.filter fun y =>
    (TM.Term.toList y).all (fun q => !lt q w)).length == 2324
#guard (deep64.flatMap fun e => deep64.filter fun y => !(mulDescb e y)).length == 0
#guard deep64.length * deep64.length == 6400

-- 肯定 6.  領域そのもの。§63.5 の `CollapseInT` 測定を (G3) の形で取り直す。
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.length == 443
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.all fun a =>
  TM.Term.inT (Trans.Dict.dict a)

end


/-! ## §65 (G1) IS FALSE AS STATED, (G2) IS TRUE — AND BOTH CLOSE

§64 reduced `CollapseInT` to three named hypotheses and recommended closing the first two.
The recommendation was checked before it was followed, and the check came back split.

  **(G1) `DivDescInT` IS FALSE — and `not_divDescInT` below PROVES it** (axioms: `propext`
  only).  Not for want of the side condition §64 already found: with it.  Smallest
  counterexample, degree sum 17:

      w = ω,   l = [ω^ω, ω]

  Every hypothesis holds — `inT ω`; both members additively principal and `inT`; `l`
  descending (`ω ≤ ω^ω`); and `lt q w = false` for BOTH members, since `ω ≤ ω ≤ ω^ω`.  But
  `divAP ω (ω^ω) = 1` while `divAP ω ω = ω`, so the image `[1, ω]` ASCENDS.  The list is not
  an artefact of the Prop's generality either: `l = toList (ω^ω ⊕ ω)` and `ω^ω ⊕ ω` is a
  genuine term of 𝔗(M).

  WHY 82373 + 2324 PAIRS MISSED IT.  §64's positive sweep quantified `l` not over lists but
  as `toList y` for `y` RANGING OVER THE CORPUS, so it only ever saw the component lists of
  corpus terms — and `ω^ω ⊕ ω` is in neither population (`corp64` closes `add` over `at64`
  only, and `ω^ω = φ̄(0,ω)` is not in `at64`).  §64's counterexample search, which did range
  over lists, stopped at `w = M` and `w = Z M` and concluded "regular does not rescue it,
  `w ≤ every member` does".  Both halves of that conclusion are right about what they tested
  and wrong as stated: the missing fact is that `w ≤ p` does NOT give `w ≤ logOm p` unless
  `w` is STRONGLY CRITICAL — at `w = p = ω`, `ω ≤ ω` but `logOm ω = 1 < ω`.

  **The repair is `w ∈ SC`, and it is exactly what the call site has**: `wcnf`'s base is
  always `reg (u+1) = Z u`, and `(Z ·).isSC` is `rfl`.  `DivDescSC` is `DivDescInT` with that
  one conjunct added, and it is PROVED, unconditionally.

  **(G2) `MulDescInT` is true exactly as §64 states it** — no side condition — and is PROVED,
  unconditionally.

WHAT CARRIES THEM.  Three monotonicity steps and one order fact, each measured before it was
proved (§65.7) and each with its own side condition, none of them decoration:

  §65.1  heads and sums at `inT`: `0 ≤ ·`, `1 ≤ ·` for nonzero, `ofList (b :: t) < a` is
         `b < a` for additively principal `a`, and HEAD MONOTONICITY — `x ≤ y` forces the
         head component of `x` below the head component of `y`.  That is what makes the
         `subAP` case analysis finite.
  §65.2  `succT` at `inT`: `p < succT p`, and `p < v → succT p ≤ v` (NOTHING lies strictly
         between `p` and `p ⊕ 1`), `splitFin` rebuilds its argument, and hence **D1**
         (`dnArg x ≤ x`) and **D2** (`x < y → x ≤ dnArg y`) of `CNVOps` §28 one notch up.
         `CNV` admits three shapes and 𝔗(M) seven; the four new ones are additively principal
         atoms and go through the `φ̄` case of §28 unchanged.  **D3 — §29's hard one — is not
         needed and not restated**: it buys strictness, and every consumer here is non-strict.
  §65.3  `ω^·` is MONOTONE on 𝔗(M).  `omegaNF_eq_gen` — `ω^x = if M < x then ω̄^x else if
         isFP 0 x then x else φ̄0(dnArg x)` — holds for EVERY term, with no hypothesis at all,
         and is where the `isFixP` of `CNVOps` §26 WIDENS: at `CNV` a fixed point of `ω^·` is
         a `φ̄αβ` with `α ≠ 0`; at `inT` every strongly critical term is one too, and
         `TM/FS.lean`'s `isFP zero` — the predicate `logOm`'s own `φ̄0·` clause already uses —
         is exactly that.  Nine cases, `ω̄^·` included, none skipped.
  §65.4  `logOm` is monotone ON THE ADDITIVELY PRINCIPAL TERMS (**false without that**:
         `Ω ⊕ Ω ≤ ω^Ω` but `logOm (Ω ⊕ Ω) = Ω ⊕ Ω > Ω`, degree sum 9); `subAP w` is monotone
         ON `{x : w ≤ x}` (**false without that**: `w = M`, `x = Ω`, `y = M`, degree sum 4);
         `plus e ·` is monotone with no side condition; and the SC step `w ∈ SC ∧ w ≤ p ⟹
         w ≤ logOm p` (**false without SC**: `w = p = 1`).
         TWO THINGS THE MEASUREMENT SETTLED THAT THE RECOMMENDATION DID NOT.  `subAP` needs
         only `w ≤ x` — the condition on the SMALLER argument — and needs `w ∈ SC` not at all
         (0 failures over 109³ triples with SC dropped).  So `w ∈ SC` is consumed in exactly
         ONE place, `lt_logOm_of_sc`, and that is the whole content of the repair.
  §65.5  (G1) as `DivDescSC`; `not_divDescInT`; and (G2) as `MulDescInT` itself.
  §65.6  the consumers.  §64.4/§64.5's `wcnf_spec`, `inT_collapse`, `inT_dict` and
         `collapseInT_of_gaps` take the FALSE `DivDescInT` as a hypothesis and therefore
         CANNOT BE APPLIED; their proofs are re-run here against `DivDescSC`.  §64.3's
         `inT_mulL`/`ltM_mulL` and §64.5's `inT_idxOf`/`stepF_inv`/`fold_inv` take only
         `MulDescInT` and are reused as they stand.  The results are `wcnf_spec_sc`,
         `inT_collapse_gap3`, `inT_dict_gap3`, `collapseInT_of_gap3` and
         `hsuccS_supply_of_gap3`: **(G3) `PsiIdxOK` is the only hypothesis left.**

WHAT IS NOT CLAIMED.  (G3) is untouched — §64 measured it FALSE on hand terms (17 of 463 at
`u = 0`) and true on `dict`'s 1805-term image, and nothing here changes either.
`DivDescInT` is not repaired, it is REFUTED, so `collapseInT_of_gaps` still carries a false
hypothesis and is not used.  Nothing here says `dict`'s image is characterised, and nothing
here is a claim about `BT.isStd`.
-/

namespace Evidence.Region

/-! ### §65.1 頭部と和 — 𝔗(M) の上の順序の道具

`le` の左が `0`、`1` が最小の非零、加法主要な右辺に対する和の比較、そして**頭部の単調性**。
最後のものが §65.4 の `subAP` の単調性を支える。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

theorem le_zero_left (t : Term) : le zero t = true := by
  show ((zero == t) || lt zero t) = true
  cases hz : ((zero : Term) == t) with
  | true => rfl
  | false =>
    rw [Bool.false_or]
    refine lt_zero_left ?_
    intro hc
    subst hc
    exact Bool.noConfusion hz

/-- `1` は 𝔗(M) の最小の非零項。 -/
theorem le_one_inT {v : Term} (hv : inT v = true) (hz : v ≠ zero) : le one v = true := by
  refine le_of_not_lt3 (inT_le_fragR v hv) (show FragR (one : Term) = true from rfl) ?_
  cases hlt : lt v one with
  | false => rfl
  | true => exact absurd (below_one v hv (fuelOf v one) hlt) hz

/-- 非和・非零に対する `⊕` の比較は頭部だけで決まる。 -/
theorem lt_ofList_nsum {a : Term} (hap : a.isAP = true) :
    ∀ (b : Term) (t : List Term), lt (ofList (b :: t)) a = lt b a := by
  intro b t
  cases t with
  | nil => rfl
  | cons c u =>
    show lt (add b (ofList (c :: u))) a = _
    exact lt_add_nsum (ne_zero_of_isAP hap) (nsum_of_isAP hap)

theorem toList_cons_hd {x b : Term} {s : List Term} (h : toList x = b :: s) :
    x = b ∨ ∃ v, x = add b v := by
  have hb : (toList x).head? = some b := by rw [h]; rfl
  cases x with
  | zero =>
    exact absurd (show b :: s = ([] : List Term) from h.symm) (List.cons_ne_nil b s)
  | M => exact Or.inl (Option.some.inj (show some (M : Term) = some b from hb))
  | omg a => exact Or.inl (Option.some.inj (show some (omg a) = some b from hb))
  | phi a c => exact Or.inl (Option.some.inj (show some (phi a c) = some b from hb))
  | psi k a => exact Or.inl (Option.some.inj (show some (psi k a) = some b from hb))
  | Z a => exact Or.inl (Option.some.inj (show some (Z a) = some b from hb))
  | add u v =>
    exact Or.inr ⟨v, by rw [Option.some.inj (show some u = some b from hb)]⟩

/-- 頭部成分は自分自身以下。 -/
theorem le_hd_self_inT {x b : Term} {s : List Term} (hx : inT x = true)
    (h : toList x = b :: s) : le b x = true := by
  rcases toList_cons_hd h with hb | ⟨v, hb⟩
  · rw [hb]; exact Evidence.WF.le_self _
  · rw [hb]
    refine le_of_lt (lt_head_add ?_ v)
    have := inT_add (by rw [← hb]; exact hx)
    exact this.1

/-- **頭部の単調性。** `x ≤ y` なら `x` の頭部は `y` の頭部以下。 -/
theorem hd_mono_inT {x y b c : Term} {s t : List Term} (hx : inT x = true) (hy : inT y = true)
    (hxl : toList x = b :: s) (hyl : toList y = c :: t) (h : le x y = true) :
    le b c = true := by
  have hib : inT b = true := inTL_inT hx b (by rw [hxl]; exact List.Mem.head _)
  have hic : inT c = true := inTL_inT hy c (by rw [hyl]; exact List.Mem.head _)
  have hapb : b.isAP = true := inTL_isAP hx b (by rw [hxl]; exact List.Mem.head _)
  cases hbc : le b c with
  | true => rfl
  | false =>
    exfalso
    have hcb : lt c b = true := lt_of_not_le_inT hib hic hbc
    have hyb : lt y b = true := by
      rw [← inT_ofList_toList y hy, hyl, lt_ofList_nsum hapb]
      exact hcb
    have hbx : le b x = true := le_hd_self_inT hx hxl
    have : lt y x = true := lt_of_lt_of_le3 (inT_le_fragR y hy) (inT_le_fragR b hib)
      (inT_le_fragR x hx) hyb hbx
    rcases (Bool.or_eq_true _ _).mp h with he | hl
    · rw [eq_of_beq he, lt_irrefl] at this; exact Bool.noConfusion this
    · rw [lt_asymm_inT hx hy hl] at this; exact Bool.noConfusion this

/-- 単調な写像は降順の列を降順に写す。 -/
theorem descL_map_mono (f : Term → Term) (P : Term → Prop)
    (hf : ∀ a b, P a → P b → le b a = true → le (f b) (f a) = true) :
    ∀ (l : List Term), (∀ x ∈ l, P x) → descL l = true → descL (l.map f) = true := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons a t ih =>
    intro hp hd
    cases t with
    | nil => rfl
    | cons b u =>
      obtain ⟨hba, hdt⟩ := descL_cons.mp hd
      refine descL_cons.mpr ⟨?_, ih (fun x hx => hp x (List.Mem.tail a hx)) hdt⟩
      exact hf a b (hp a (List.Mem.head _)) (hp b (List.Mem.tail a (List.Mem.head _))) hba

end

/-! ### §65.2 `succT` と `splitFin` — D1 と D2 を 𝔗(M) の上で

`CNVOps` §28 は `CNV` の 3 形 (`0`, `φ̄`, `⊕`) しか見ない。𝔗(M) には `M`, `ω̄^·`, `ψ`, `Z`
の 4 形が増えるが、そのどれも**加法主要な原子**であって `⊕` の頭部と同じ扱いで済む
(`le_succT_atom`)。`splitFin_rebuild` は `plus_ofNat` の成分列を直接計算する形に書き換えた
——`CNV` 版の `plus_ofNat_spec` は `cnv_succT` を経由するが、その必要はない。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

/-- `p < p ⊕ 1`。 -/
theorem lt_succT_inT : ∀ (p : Term), inT p = true → lt p (succT p) = true := by
  intro p
  induction p with
  | zero => intro _; exact lt_zero_left (by intro hc; exact Term.noConfusion hc)
  | M => intro _; exact lt_head_add rfl one
  | omg _ _ => intro _; exact lt_head_add rfl one
  | phi _ _ _ _ => intro _; exact lt_head_add rfl one
  | psi _ _ _ _ => intro _; exact lt_head_add rfl one
  | Z _ _ => intro _; exact lt_head_add rfl one
  | add s t _ iht =>
    intro h
    obtain ⟨_, _, hit, _⟩ := inT_add h
    have hrec := iht hit
    have hne : add s t ≠ add s (succT t) := by
      intro hc
      injection hc with _ h2
      rw [← h2, lt_irrefl] at hrec
      exact Bool.noConfusion hrec
    show lt (add s t) (add s (succT t)) = true
    rw [lt_add_add hne, if_pos rfl]
    exact hrec

theorem toList_ne_nil_inT {d : Term} (hz : d ≠ zero) : toList d ≠ [] := by
  intro hc
  exact hz (toList_eq_nil d hc)

/-- 末尾に `1` を継ぎ足すのは `succT`。 -/
theorem ofList_toList_snoc_inT : ∀ (a : Term), inT a = true →
    ofList (toList a ++ [one]) = succT a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | M => intro _; rfl
  | omg _ _ => intro _; rfl
  | phi _ _ _ _ => intro _; rfl
  | psi _ _ _ _ => intro _; rfl
  | Z _ _ => intro _; rfl
  | add c d _ ihd =>
    intro h
    obtain ⟨_, _, hid, hdesc⟩ := inT_add h
    have hdz : d ≠ zero := by intro hc; rw [hc] at hdesc; exact Bool.noConfusion hdesc
    show ofList (c :: (toList d ++ [one])) = add c (succT d)
    cases hl : toList d with
    | nil => exact absurd hl (toList_ne_nil_inT hdz)
    | cons e rest =>
      show add c (ofList (e :: (rest ++ [one]))) = add c (succT d)
      rw [show (e :: (rest ++ [one])) = toList d ++ [one] from by rw [hl]; rfl, ihd hid]

/-- 非和の右辺に対しては、和は頭部だけで決まる。 -/
theorem le_add_of_lt_nsum {a e v : Term} (hv : NSum v = true) (hvz : v ≠ zero)
    (hlt : lt a v = true) : le (add a e) v = true :=
  le_of_lt (by rw [lt_add_nsum hvz hv]; exact hlt)

/-- 加法主要な原子に対する `≤ succ`。 -/
theorem le_succT_atom {a : Term} (hap : a.isAP = true) {v : Term} (hv : inT v = true)
    (hlt : lt a v = true) : le (add a one) v = true := by
  cases v with
  | zero => rw [lt_zero_right] at hlt; exact Bool.noConfusion hlt
  | M => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | omg _ => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | phi _ _ => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | psi _ _ => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | Z _ => exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
  | add c d =>
    rw [Evidence.Cert.lt_ap_add hap] at hlt
    obtain ⟨_, _, hid, hdesc⟩ := inT_add hv
    by_cases hac : a = c
    · rw [hac]
      refine le_add_tail (le_one_inT hid ?_)
      intro hz; rw [hz] at hdesc; exact Bool.noConfusion hdesc
    · refine le_of_lt (lt_add_head hac ?_)
      rcases (Bool.or_eq_true _ _).mp hlt with he | hl
      · exact absurd (eq_of_beq he) hac
      · exact hl

/-- **`p` と `p ⊕ 1` のあいだには何も無い** — 𝔗(M) の上で。`CNVOps` §28 が `CNV` で言う
    `le_succT_of_lt` の 𝔗(M) 版。 -/
theorem le_succT_of_lt_inT : ∀ (a : Term), inT a = true → ∀ (v : Term), inT v = true →
    lt a v = true → le (succT a) v = true := by
  intro a
  induction a with
  | zero =>
    intro _ v hv hlt
    show le one v = true
    refine le_one_inT hv ?_
    intro hc
    rw [hc, lt_irrefl] at hlt
    exact Bool.noConfusion hlt
  | M => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | omg _ _ => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | phi _ _ _ _ => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | psi _ _ _ _ => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | Z _ _ => intro _ v hv hlt; exact le_succT_atom rfl hv hlt
  | add s t _ iht =>
    intro ha v hv hlt
    obtain ⟨_, _, hit, _⟩ := inT_add ha
    show le (add s (succT t)) v = true
    cases v with
    | zero => rw [lt_zero_right] at hlt; exact Bool.noConfusion hlt
    | M =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | omg _ =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | phi _ _ =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | psi _ _ =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | Z _ =>
      rw [lt_add_nsum (by intro hc; exact Term.noConfusion hc) rfl] at hlt
      exact le_add_of_lt_nsum rfl (by intro hc; exact Term.noConfusion hc) hlt
    | add c d =>
      obtain ⟨_, _, hid, _⟩ := inT_add hv
      by_cases heq : add s t = add c d
      · rw [heq, lt_irrefl] at hlt; exact Bool.noConfusion hlt
      · rw [lt_add_add heq] at hlt
        by_cases hsc : s = c
        · rw [if_pos hsc] at hlt
          rw [hsc]
          exact le_add_tail (iht hit d hid hlt)
        · rw [if_neg hsc] at hlt
          exact le_of_lt (lt_add_head hsc hlt)

/-! `plus g (ofNat m)` の成分列 — `1` を `m` 個継ぎ足すだけ。 -/

theorem filter_one_toList_inT {a : Term} (h : inT a = true) :
    (toList a).filter (fun x => le one x) = toList a :=
  filter_self_of_all _ _ (fun x hx => Evidence.Cert.le_one_ap (inTL_isAP h x hx))

theorem plus_ofNat_eq_inT {g : Term} (hg : inT g = true) (k : Nat) :
    plus g (ofNat (k + 1)) = ofList (toList g ++ List.replicate (k + 1) one) := by
  have hl : toList (ofNat (k + 1)) = one :: List.replicate k one := by
    rw [toList_ofNat (k + 1)]; rfl
  rw [plus_eq hl, filter_one_toList_inT hg, toList_ofNat (k + 1)]

theorem toList_plus_ofNat_inT {g : Term} (hg : inT g = true) : ∀ m,
    toList (plus g (ofNat m)) = toList g ++ List.replicate m one := by
  intro m
  cases m with
  | zero =>
    show toList (plus g zero) = toList g ++ []
    exact (List.append_nil _).symm
  | succ k =>
    rw [plus_ofNat_eq_inT hg k]
    refine toList_ofList _ ?_
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact inTL_isAP hg x h
    · rw [List.eq_of_mem_replicate h]; rfl

theorem plus_ofNat_step_inT {g : Term} (hg : inT g = true) (m : Nat) :
    plus g (ofNat (m + 1)) = succT (plus g (ofNat m)) := by
  rw [plus_ofNat_eq_inT hg m, ← ofList_toList_snoc_inT _ (inT_plus hg (inT_ofNat m)),
    toList_plus_ofNat_inT hg m, List.append_assoc, ← List.replicate_succ']

/-- **`splitFin` は引数を組み立て直す** — 𝔗(M) の上で。 -/
theorem splitFin_rebuild_inT (t : Term) (ht : inT t = true) :
    plus (splitFin t).1 (ofNat (splitFin t).2) = t := by
  have hcg : inT (splitFin t).1 = true := inT_splitFin ht
  have hF1 : ((toList t).reverse.dropWhile (fun x => x == one)).reverse
      ++ List.replicate (((toList t).reverse.takeWhile (fun x => x == one)).length) one
      = toList t := by
    have h := trailing_ones (toList t).reverse
    rwa [List.reverse_reverse] at h
  have hAP : ∀ x ∈ ((toList t).reverse.dropWhile (fun x => x == one)).reverse,
      x.isAP = true := by
    intro x hx
    exact inTL_isAP ht x (by rw [← hF1]; exact List.mem_append_left _ hx)
  have hg : toList (splitFin t).1
      = ((toList t).reverse.dropWhile (fun x => x == one)).reverse := by
    rw [splitFin_fst t, toList_ofList _ hAP]
  have hto : toList (plus (splitFin t).1 (ofNat (splitFin t).2)) = toList t := by
    rw [toList_plus_ofNat_inT hcg, hg]
    exact hF1
  rw [← inT_ofList_toList _ (inT_plus hcg (inT_ofNat _)), hto, inT_ofList_toList t ht]

theorem inT_dnArg {x : Term} (hx : inT x = true) : inT (dnArg x) = true := by
  have hg : inT (splitFin x).1 = true := inT_splitFin hx
  cases hs : splitFin x with
  | mk g m =>
    rw [hs] at hg
    rcases dnArg_or hs with h | ⟨_, h⟩
    · rw [h]; exact hx
    · rw [h]; exact inT_plus hg (inT_ofNat _)

/-- **D1** — `dnArg` は下げるだけ (𝔗(M) 版)。 -/
theorem dnArg_le_inT {x : Term} (hx : inT x = true) : le (dnArg x) x = true := by
  cases hs : splitFin x with
  | mk g m =>
    rcases dnArg_or hs with h | ⟨hm, h⟩
    · rw [h]; exact Evidence.WF.le_self _
    · have hcg : inT g = true := by
        have h0 := inT_splitFin hx; rw [hs] at h0; exact h0
      have hreb : plus g (ofNat m) = x := by
        have h0 := splitFin_rebuild_inT x hx; rw [hs] at h0; exact h0
      cases m with
      | zero => exact absurd hm (by omega)
      | succ k =>
        rw [h, ← hreb, show k + 1 - 1 = k from rfl, plus_ofNat_step_inT hcg k]
        exact le_of_lt (lt_succT_inT _ (inT_plus hcg (inT_ofNat k)))

/-- **D2** — 下げるのは高々 1 (𝔗(M) 版)。 -/
theorem dnArg_ge_inT {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : lt x y = true) : le x (dnArg y) = true := by
  cases hs : splitFin y with
  | mk g m =>
    rcases dnArg_or hs with hd | ⟨hm, hd⟩
    · rw [hd]; exact le_of_lt h
    · have hcg : inT g = true := by
        have h0 := inT_splitFin hy; rw [hs] at h0; exact h0
      have hreb : plus g (ofNat m) = y := by
        have h0 := splitFin_rebuild_inT y hy; rw [hs] at h0; exact h0
      cases m with
      | zero => exact absurd hm (by omega)
      | succ k =>
        have hz : inT (plus g (ofNat k)) = true := inT_plus hcg (inT_ofNat k)
        have hy' : y = succT (plus g (ofNat k)) := by
          rw [← hreb, plus_ofNat_step_inT hcg k]
        rw [hd, show k + 1 - 1 = k from rfl]
        cases hle : le x (plus g (ofNat k)) with
        | true => rfl
        | false =>
          exfalso
          have hlt : lt (plus g (ofNat k)) x = true := lt_of_not_le_inT hx hz hle
          have hs2 : le y x = true := by
            rw [hy']; exact le_succT_of_lt_inT _ hz x hx hlt
          have hcon := lt_of_le_of_lt3 (inT_le_fragR y hy) (inT_le_fragR x hx)
            (inT_le_fragR y hy) hs2 h
          rw [lt_irrefl] at hcon
          exact Bool.noConfusion hcon

end

/-! ### §65.3 `ω^·` は 𝔗(M) の上で単調

`CNVOps` §26 は `CNV` の上で `ω^x = if isFixP x then x else φ̄0(dnArg x)` と書く。𝔗(M) では
枝が 2 つ増える: `M < x` の `ω̄^x` と、**不動点の範囲が広がる**こと。`CNV` では不動点は
`φ̄αβ` (`α ≠ 0`) だけだが、𝔗(M) では `M`・`ψκα`・`Zα` — 強臨界項はすべて自分自身が
`ω` の指数である。その述語は `TM/FS.lean` の `isFP zero` がすでにそのもので、`logOm` の
`φ̄0·` 節が使っているのと同じものである。

D3 (`CNVOps` §29) は使わない。結論が `le` であって `lt` ではないからで、`dnArg` が 2 つの
引数を潰しても困らない。 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

theorem lt_eq_ltF_succ (s t : Term) : lt s t = ltF (2 * (s.deg + t.deg) + 7 + 1) s t := by
  rw [lt_eq_ltF s t (2 * (s.deg + t.deg) + 7 + 1) (by omega)]

/-- **`ω^·` の 3 つの形**、側条件なし。`isFP zero` が `CNVOps` §26 の `isFixP` の
    𝔗(M) 版 — 強臨界項もまた `ω^·` の不動点である。 -/
theorem phiNF_zero_eq_gen (x : Term) :
    (if x == M then M else phiNF zero x)
      = (if TM.Term.isFP zero x then x else phi zero (dnArg x)) := by
  cases x with
  | zero => exact phiNFsucc_zero_eq zero
  | omg a => exact phiNFsucc_zero_eq (omg a)
  | add u v => exact phiNFsucc_zero_eq (add u v)
  | M =>
    have h1 : TM.Term.isFP zero M = true := by
      unfold TM.Term.isFP
      rw [lt_zero_M]
      rfl
    rw [h1]
    rfl
  | psi k a =>
    have hz : lt zero (psi k a) = true := lt_zero_left (by intro hc; exact Term.noConfusion hc)
    have h1 : TM.Term.isFP zero (psi k a) = true := by
      unfold TM.Term.isFP
      rw [hz]
      rfl
    rw [h1]
    show phiNF zero (psi k a) = psi k a
    unfold phiNF
    rw [hz]
    rfl
  | Z a =>
    have hz : lt zero (Z a) = true := lt_zero_left (by intro hc; exact Term.noConfusion hc)
    have h1 : TM.Term.isFP zero (Z a) = true := by
      unfold TM.Term.isFP
      rw [hz]
      rfl
    rw [h1]
    show phiNF zero (Z a) = Z a
    unfold phiNF
    rw [hz]
    rfl
  | phi c d =>
    have h1 : TM.Term.isFP zero (phi c d) = lt zero c := by
      unfold TM.Term.isFP; rfl
    rw [h1]
    show (if lt zero c then phi c d else phiNFsucc zero (phi c d))
        = (if lt zero c then phi c d else phi zero (dnArg (phi c d)))
    by_cases hc : lt zero c = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      exact phiNFsucc_zero_eq (phi c d)

theorem omegaNF_eq_gen (x : Term) :
    omegaNF x = if lt M x then omg x
                else if TM.Term.isFP zero x then x else phi zero (dnArg x) := by
  show (if lt M x then omg x else if x == M then M else phiNF zero x) = _
  rw [phiNF_zero_eq_gen x]

/-! `ω̄^·` の枝に落ちるときの比較 (2.3.2, 2.3.3, 2.3.12)。 -/

theorem lt_phi_omg (a b y : Term) : lt (phi a b) (omg y) = true := by
  rw [lt_eq_ltF_succ]; exact ltF_succ_phi_omg _ _ _ _

theorem lt_isFP_omg {x y : Term} (hfix : TM.Term.isFP zero x = true) :
    lt x (omg y) = true := by
  cases x with
  | zero => exact Bool.noConfusion hfix
  | omg _ => exact Bool.noConfusion hfix
  | add _ _ => exact Bool.noConfusion hfix
  | M => rw [lt_eq_ltF_succ]; exact ltF_succ_M_omg _ _
  | psi k a => rw [lt_eq_ltF_succ]; exact ltF_succ_psi_omg _ _ _ _
  | Z a => rw [lt_eq_ltF_succ]; exact ltF_succ_Z_omg _ _ _
  | phi a b => exact lt_phi_omg a b y

theorem lt_omg_omg {x y : Term} (h : lt x y = true) : lt (omg x) (omg y) = true := by
  have hne : omg x ≠ omg y := by
    intro hc
    injection hc with h1
    rw [h1, lt_irrefl] at h
    exact Bool.noConfusion h
  rw [lt_eq_ltF_succ, ltF_succ_omg_omg _ hne,
    ← lt_eq_ltF x y _ (by show x.deg + y.deg ≤ 2 * ((1 + x.deg) + (1 + y.deg)) + 7; omega)]
  exact h

/-! 2.3.4 と 2.3.5 — 強臨界項と `φ̄` のあいだ。 -/

theorem lt_psi_phi_of_le {k a c w : Term} (h : le (psi k a) w = true) :
    lt (psi k a) (phi c w) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_psi_phi,
    show ltF (2 * ((psi k a).deg + (phi c w).deg) + 7) (psi k a) w = lt (psi k a) w from
      (lt_eq_ltF (psi k a) w _ (by
        show (1 + k.deg + a.deg) + w.deg
          ≤ 2 * ((1 + k.deg + a.deg) + (1 + c.deg + w.deg)) + 7
        omega)).symm]
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [he, Bool.or_true, Bool.true_or, Bool.true_or]
  · rw [hl, Bool.or_true]

theorem lt_Z_phi_of_le {e c w : Term} (h : le (Z e) w = true) :
    lt (Z e) (phi c w) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_Z_phi,
    show ltF (2 * ((Z e).deg + (phi c w).deg) + 7) (Z e) w = lt (Z e) w from
      (lt_eq_ltF (Z e) w _ (by
        show (1 + e.deg) + w.deg ≤ 2 * ((1 + e.deg) + (1 + c.deg + w.deg)) + 7
        omega)).symm]
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [he, Bool.or_true, Bool.true_or, Bool.true_or]
  · rw [hl, Bool.or_true]

theorem lt_phi_psi_of {a b k c : Term} (h1 : lt a (psi k c) = true)
    (h2 : lt b (psi k c) = true) : lt (phi a b) (psi k c) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_psi,
    show ltF (2 * ((phi a b).deg + (psi k c).deg) + 7) a (psi k c) = lt a (psi k c) from
      (lt_eq_ltF a (psi k c) _ (by
        show a.deg + (1 + k.deg + c.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + k.deg + c.deg)) + 7
        omega)).symm,
    show ltF (2 * ((phi a b).deg + (psi k c).deg) + 7) b (psi k c) = lt b (psi k c) from
      (lt_eq_ltF b (psi k c) _ (by
        show b.deg + (1 + k.deg + c.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + k.deg + c.deg)) + 7
        omega)).symm, h1, h2]
  rfl

theorem lt_phi_Z_of {a b d : Term} (h1 : lt a (Z d) = true)
    (h2 : lt b (Z d) = true) : lt (phi a b) (Z d) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_Z,
    show ltF (2 * ((phi a b).deg + (Z d).deg) + 7) a (Z d) = lt a (Z d) from
      (lt_eq_ltF a (Z d) _ (by
        show a.deg + (1 + d.deg) ≤ 2 * ((1 + a.deg + b.deg) + (1 + d.deg)) + 7
        omega)).symm,
    show ltF (2 * ((phi a b).deg + (Z d).deg) + 7) b (Z d) = lt b (Z d) from
      (lt_eq_ltF b (Z d) _ (by
        show b.deg + (1 + d.deg) ≤ 2 * ((1 + a.deg + b.deg) + (1 + d.deg)) + 7
        omega)).symm, h1, h2]
  rfl

/-- 不動点は `φ̄0w` の下 — `x ≤ w` があれば。`x = M` だけは除く (`M < φ̄0w` は偽)。 -/
theorem lt_isFP_phi_zero {x w : Term} (hfix : TM.Term.isFP zero x = true) (hne : x ≠ M)
    (h : le x w = true) : lt x (phi zero w) = true := by
  cases x with
  | zero => exact Bool.noConfusion hfix
  | omg _ => exact Bool.noConfusion hfix
  | add _ _ => exact Bool.noConfusion hfix
  | M => exact absurd rfl hne
  | psi k a => exact lt_psi_phi_of_le h
  | Z e => exact lt_Z_phi_of_le h
  | phi c d =>
    have hc : lt zero c = true := by
      have h1 : TM.Term.isFP zero (phi c d) = lt zero c := by unfold TM.Term.isFP; rfl
      rw [h1] at hfix; exact hfix
    have hzc : ¬ (c = zero) := by
      intro hcc
      rw [hcc, lt_irrefl] at hc
      exact Bool.noConfusion hc
    have hnn : phi c d ≠ phi zero w := by
      intro hcc
      injection hcc with h1 _
      exact hzc h1
    rw [lt_phi_phi hnn, if_neg hzc,
      if_neg (by rw [lt_zero_right]; exact Bool.noConfusion)]
    exact h

/-- `φ̄0z` は不動点 `y` の下 — `z < y` があれば。 -/
theorem lt_phi_zero_isFP {z y : Term} (hfix : TM.Term.isFP zero y = true)
    (h : lt z y = true) : lt (phi zero z) y = true := by
  cases y with
  | zero => exact Bool.noConfusion hfix
  | omg _ => exact Bool.noConfusion hfix
  | add _ _ => exact Bool.noConfusion hfix
  | M => exact lt_phi_M zero z
  | psi k a =>
    exact lt_phi_psi_of (lt_zero_left (by intro hc; exact Term.noConfusion hc)) h
  | Z e =>
    exact lt_phi_Z_of (lt_zero_left (by intro hc; exact Term.noConfusion hc)) h
  | phi c d =>
    have hc : lt zero c = true := by
      have h1 : TM.Term.isFP zero (phi c d) = lt zero c := by unfold TM.Term.isFP; rfl
      rw [h1] at hfix; exact hfix
    have hzc : ¬ ((zero : Term) = c) := by
      intro hcc
      rw [← hcc, lt_irrefl] at hc
      exact Bool.noConfusion hc
    have hnn : phi zero z ≠ phi c d := by
      intro hcc
      injection hcc with h1 _
      exact hzc h1
    rw [lt_phi_phi hnn, if_neg hzc, if_pos hc]
    exact h

theorem le_phi_zero_arg {a b : Term} (h : le a b = true) :
    le (phi zero a) (phi zero b) = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [eq_of_beq he]; exact Evidence.WF.le_self _
  · exact le_of_lt (lt_phi_arg hl)

/-- **`ω^·` は 𝔗(M) の上で単調** (非狭義)。D1 と D2 だけを使い、D3 は使わない。 -/
theorem le_omegaNF_of_lt_inT {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : lt x y = true) : le (omegaNF x) (omegaNF y) = true := by
  rw [omegaNF_eq_gen x, omegaNF_eq_gen y]
  by_cases hMy : lt M y = true
  · rw [if_pos hMy]
    by_cases hMx : lt M x = true
    · rw [if_pos hMx]; exact le_of_lt (lt_omg_omg h)
    · rw [if_neg hMx]
      by_cases hfx : TM.Term.isFP zero x = true
      · rw [if_pos hfx]; exact le_of_lt (lt_isFP_omg hfx)
      · rw [if_neg hfx]; exact le_of_lt (lt_phi_omg _ _ _)
  · rw [if_neg hMy]
    have hMx : ¬ (lt M x = true) := by
      intro hc
      exact hMy (lt_trans_inT inT_M hx hy hc h)
    rw [if_neg hMx]
    have hxM : x ≠ M := by
      intro hc
      rw [hc] at h
      exact hMy h
    by_cases hfx : TM.Term.isFP zero x = true
    · rw [if_pos hfx]
      by_cases hfy : TM.Term.isFP zero y = true
      · rw [if_pos hfy]; exact le_of_lt h
      · rw [if_neg hfy]
        exact le_of_lt (lt_isFP_phi_zero hfx hxM (dnArg_ge_inT hx hy h))
    · rw [if_neg hfx]
      by_cases hfy : TM.Term.isFP zero y = true
      · rw [if_pos hfy]
        refine le_of_lt (lt_phi_zero_isFP hfy ?_)
        exact lt_of_le_of_lt3 (inT_le_fragR _ (inT_dnArg hx)) (inT_le_fragR x hx)
          (inT_le_fragR y hy) (dnArg_le_inT hx) h
      · rw [if_neg hfy]
        refine le_phi_zero_arg ?_
        exact le_trans_inT (inT_dnArg hx) hx (inT_dnArg hy)
          (dnArg_le_inT hx) (dnArg_ge_inT hx hy h)

theorem omegaNF_mono_inT {x y : Term} (hx : inT x = true) (hy : inT y = true)
    (h : le x y = true) : le (omegaNF x) (omegaNF y) = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · rw [eq_of_beq he]; exact Evidence.WF.le_self _
  · exact le_omegaNF_of_lt_inT hx hy hl

end

/-! ### §65.4 `logOm`・`subAP`・`plus` の単調性、そして SC の一段

3 つとも側条件つきで、どれも側条件を落とすと偽 (§65.7 に反例を凍結)。

  `logOm`  加法主要な項の上でのみ単調。`Ω ⊕ Ω ≤ ω^Ω` だが `logOm (Ω ⊕ Ω) = Ω ⊕ Ω > Ω`。
  `subAP`  `w ≤ x` と `w ≤ y` の上でのみ単調。`w = M`, `x = Ω`, `y = M` が最小反例。
  `plus`   側条件なし。
  SC の一段  `w ∈ SC` かつ `w ≤ p` (`p` は加法主要) なら `w ≤ logOm p`。**これが (G1) の
           側条件が `w ∈ SC` でなければならない理由**で、`w = p = 1` で破れる。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (logOm subAP divAP mulL)

theorem plus_one_eq_succT_inT {a : Term} (ha : inT a = true) : plus a one = succT a := by
  rw [plus_eq (show toList (one : Term) = [one] from rfl), filter_one_toList_inT ha]
  exact ofList_toList_snoc_inT a ha

theorem inT_succT_inT {a : Term} (ha : inT a = true) : inT (succT a) = true := by
  rw [← plus_one_eq_succT_inT ha]
  exact inT_plus ha inT_one

/-! 2.3.4/2.3.5 の逆読み — `φ̄` と強臨界項のあいだの比較から引数の比較を取り出す。 -/

theorem lt_arg_of_phi_lt_psi {a b k c : Term} (h : lt (phi a b) (psi k c) = true) :
    lt b (psi k c) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_psi,
    show ltF (2 * ((phi a b).deg + (psi k c).deg) + 7) b (psi k c) = lt b (psi k c) from
      (lt_eq_ltF b (psi k c) _ (by
        show b.deg + (1 + k.deg + c.deg)
          ≤ 2 * ((1 + a.deg + b.deg) + (1 + k.deg + c.deg)) + 7
        omega)).symm] at h
  exact ((Bool.and_eq_true _ _).mp h).2

theorem lt_arg_of_phi_lt_Z {a b d : Term} (h : lt (phi a b) (Z d) = true) :
    lt b (Z d) = true := by
  rw [lt_eq_ltF_succ, ltF_succ_phi_Z,
    show ltF (2 * ((phi a b).deg + (Z d).deg) + 7) b (Z d) = lt b (Z d) from
      (lt_eq_ltF b (Z d) _ (by
        show b.deg + (1 + d.deg) ≤ 2 * ((1 + a.deg + b.deg) + (1 + d.deg)) + 7
        omega)).symm] at h
  exact ((Bool.and_eq_true _ _).mp h).2

theorem le_of_psi_lt_phi_zero {k a e : Term} (h : lt (psi k a) (phi zero e) = true) :
    le (psi k a) e = true := by
  rw [lt_eq_ltF_succ, ltF_succ_psi_phi,
    show ltF (2 * ((psi k a).deg + (phi zero e).deg) + 7) (psi k a) e = lt (psi k a) e from
      (lt_eq_ltF (psi k a) e _ (by
        show (1 + k.deg + a.deg) + e.deg
          ≤ 2 * ((1 + k.deg + a.deg) + (1 + (zero : Term).deg + e.deg)) + 7
        omega)).symm,
    show ((psi k a) == (zero : Term)) = false from rfl, ltF_right_zero,
    Bool.false_or, Bool.or_false] at h
  exact h

theorem le_of_Z_lt_phi_zero {d e : Term} (h : lt (Z d) (phi zero e) = true) :
    le (Z d) e = true := by
  rw [lt_eq_ltF_succ, ltF_succ_Z_phi,
    show ltF (2 * ((Z d).deg + (phi zero e).deg) + 7) (Z d) e = lt (Z d) e from
      (lt_eq_ltF (Z d) e _ (by
        show (1 + d.deg) + e.deg
          ≤ 2 * ((1 + d.deg) + (1 + (zero : Term).deg + e.deg)) + 7
        omega)).symm,
    show ((Z d) == (zero : Term)) = false from rfl, ltF_right_zero,
    Bool.false_or, Bool.or_false] at h
  exact h

theorem le_arg_of_le_pow {b d : Term} (h : le (phi zero b) (phi zero d) = true) :
    le b d = true := by
  rcases (Bool.or_eq_true _ _).mp h with he | hl
  · have hq := eq_of_beq he
    injection hq with _ h2
    rw [h2]
    exact Evidence.WF.le_self _
  · rw [lt_pow] at hl
    exact le_of_lt hl

/-! `logOm (φ̄0b)` は `b` か `b ⊕ 1`。どちらでも `b < y` から `logOm (φ̄0b) ≤ y` が出る。 -/

theorem le_shift_of_lt {b y : Term} (hb : inT b = true) (hy : inT y = true)
    (h : lt b y = true) : le (logOm (phi zero b)) y = true := by
  show le (if TM.Term.phiShifted zero b then plus b one else b) y = true
  by_cases hs : TM.Term.phiShifted zero b = true
  · rw [if_pos hs, plus_one_eq_succT_inT hb]
    exact le_succT_of_lt_inT b hb y hy h
  · rw [if_neg hs]
    exact le_of_lt h

theorem le_logOm_phi_zero_of_le {x e : Term} (hx : inT x = true) (he : inT e = true)
    (h : le x e = true) : le x (logOm (phi zero e)) = true := by
  show le x (if TM.Term.phiShifted zero e then plus e one else e) = true
  by_cases hs : TM.Term.phiShifted zero e = true
  · rw [if_pos hs]
    refine le_trans_inT hx he (inT_plus he inT_one) h ?_
    rw [plus_one_eq_succT_inT he]
    exact le_of_lt (lt_succT_inT e he)
  · rw [if_neg hs]
    exact h

theorem le_shift_shift {b d : Term} (hb : inT b = true) (hd : inT d = true)
    (h : le b d = true) :
    le (logOm (phi zero b)) (logOm (phi zero d)) = true := by
  show le (if TM.Term.phiShifted zero b then plus b one else b)
         (if TM.Term.phiShifted zero d then plus d one else d) = true
  by_cases hsb : TM.Term.phiShifted zero b = true
  · rw [if_pos hsb, plus_one_eq_succT_inT hb]
    by_cases hsd : TM.Term.phiShifted zero d = true
    · rw [if_pos hsd, plus_one_eq_succT_inT hd]
      rcases (Bool.or_eq_true _ _).mp h with he | hl
      · rw [eq_of_beq he]; exact Evidence.WF.le_self _
      · exact le_trans_inT (inT_succT_inT hb) hd (inT_succT_inT hd)
          (le_succT_of_lt_inT b hb d hd hl) (le_of_lt (lt_succT_inT d hd))
    · rw [if_neg hsd]
      have hne : b ≠ d := by
        intro hc
        rw [hc] at hsb
        exact hsd hsb
      exact le_succT_of_lt_inT b hb d hd (lt_of_le_of_ne h hne)
  · rw [if_neg hsb]
    by_cases hsd : TM.Term.phiShifted zero d = true
    · rw [if_pos hsd]
      refine le_trans_inT hb hd (inT_plus hd inT_one) h ?_
      rw [plus_one_eq_succT_inT hd]
      exact le_of_lt (lt_succT_inT d hd)
    · rw [if_neg hsd]
      exact h


/-- `logOm` は `φ̄0·` 以外の形では恒等。 -/
theorem logOm_eq_self_of_ne : ∀ (x : Term), (∀ b, x ≠ phi zero b) → logOm x = x := by
  intro x hne
  cases x with
  | zero => rfl
  | M => rfl
  | omg _ => rfl
  | psi _ _ => rfl
  | Z _ => rfl
  | add _ _ => rfl
  | phi c d =>
    cases c with
    | zero => exact absurd rfl (hne d)
    | M => rfl
    | omg _ => rfl
    | phi _ _ => rfl
    | psi _ _ => rfl
    | Z _ => rfl
    | add _ _ => rfl

/-- `c ≠ 0` の `φ̄cd` が `φ̄0e` の下なら `φ̄cd ≤ e` (2.3.13(iii))。 -/
theorem le_of_phi_lt_phi_zero {c d e : Term} (hc : ¬ (c = zero))
    (hlt : lt (phi c d) (phi zero e) = true) : le (phi c d) e = true := by
  have hne : phi c d ≠ phi zero e := by
    intro hcc
    injection hcc with h1 _
    exact hc h1
  rw [lt_phi_phi hne, if_neg hc,
    if_neg (by rw [lt_zero_right]; exact Bool.noConfusion)] at hlt
  exact hlt

/-- `φ̄0b < φ̄ce` (`c ≠ 0`) なら `b < φ̄ce` (2.3.13(i))。 -/
theorem lt_arg_of_pow_lt_phi {b c e : Term} (hc : ¬ ((zero : Term) = c))
    (hlt : lt (phi zero b) (phi c e) = true) : lt b (phi c e) = true := by
  have hne : phi zero b ≠ phi c e := by
    intro hcc
    injection hcc with h1 _
    exact hc h1
  rw [lt_phi_phi hne, if_neg hc, if_pos (lt_zero_left (fun hcc => hc hcc.symm))] at hlt
  exact hlt

/-- `logOm x = x` の側の単調性。`hkey` は「`x < φ̄0e` なら `x ≤ e`」で、`x` の形ごとに供給する。 -/
theorem logOm_mono_self {x y : Term} (hlx : logOm x = x) (hxne : ∀ e, x ≠ phi zero e)
    (hkey : ∀ e, lt x (phi zero e) = true → le x e = true)
    (hx : inT x = true) (hy : inT y = true) (hya : y.isAP = true) (h : le x y = true) :
    le (logOm x) (logOm y) = true := by
  rw [hlx]
  cases y with
  | zero => exact Bool.noConfusion hya
  | add _ _ => exact Bool.noConfusion hya
  | M => exact h
  | omg _ => exact h
  | psi _ _ => exact h
  | Z _ => exact h
  | phi c e =>
    cases c with
    | zero =>
      refine le_logOm_phi_zero_of_le hx (inT_phi4 hy).2.1 ?_
      exact hkey e (lt_of_le_of_ne h (hxne e))
    | M => exact h
    | omg _ => exact h
    | phi _ _ => exact h
    | psi _ _ => exact h
    | Z _ => exact h
    | add _ _ => exact h

/-- `x = φ̄0b` の側の単調性。 -/
theorem logOm_mono_pow {b y : Term} (hx : inT (phi zero b) = true) (hy : inT y = true)
    (hya : y.isAP = true) (h : le (phi zero b) y = true) :
    le (logOm (phi zero b)) (logOm y) = true := by
  have hib : inT b = true := (inT_phi4 hx).2.1
  have hbM : lt b M = true := (inT_phi4 hx).2.2.2
  cases y with
  | zero => exact Bool.noConfusion hya
  | add _ _ => exact Bool.noConfusion hya
  | M => exact le_shift_of_lt hib inT_M hbM
  | omg a =>
    refine le_shift_of_lt hib hy ?_
    exact lt_trans_inT hib inT_M hy hbM (by rw [lt_eq_ltF_succ]; exact ltF_succ_M_omg _ _)
  | psi k a =>
    refine le_shift_of_lt hib hy ?_
    exact lt_arg_of_phi_lt_psi (lt_of_le_of_ne h (by intro hc; exact Term.noConfusion hc))
  | Z d =>
    refine le_shift_of_lt hib hy ?_
    exact lt_arg_of_phi_lt_Z (lt_of_le_of_ne h (by intro hc; exact Term.noConfusion hc))
  | phi c e =>
    cases c with
    | zero => exact le_shift_shift hib (inT_phi4 hy).2.1 (le_arg_of_le_pow h)
    | M =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | omg _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | phi _ _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | psi _ _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | Z _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)
    | add _ _ =>
      refine le_shift_of_lt hib hy (lt_arg_of_pow_lt_phi ?_ ?_)
      · intro hc; exact Term.noConfusion hc
      · exact lt_of_le_of_ne h (by intro hc; injection hc with h1 _; exact Term.noConfusion h1)

/-- **`logOm` は加法主要な項の上で単調。** 加法主要を落とすと偽 (§65.7)。 -/
theorem logOm_mono_inT {x y : Term} (hxa : x.isAP = true) (hya : y.isAP = true)
    (hx : inT x = true) (hy : inT y = true) (h : le x y = true) :
    le (logOm x) (logOm y) = true := by
  cases x with
  | zero => exact Bool.noConfusion hxa
  | add _ _ => exact Bool.noConfusion hxa
  | M =>
    refine logOm_mono_self rfl (fun e hc => Term.noConfusion hc) (fun e hlt => ?_) hx hy hya h
    exact absurd hlt (by
      rw [show lt (M : Term) (phi zero e) = false from by
        rw [lt_eq_ltF_succ]; exact ltF_succ_M_phi _ _ _]
      exact Bool.noConfusion)
  | omg a =>
    refine logOm_mono_self rfl (fun e hc => Term.noConfusion hc) (fun e hlt => ?_) hx hy hya h
    exact absurd hlt (by
      rw [show lt (omg a) (phi zero e) = false from by
        rw [lt_eq_ltF_succ]; exact ltF_succ_omg_phi _ _ _ _]
      exact Bool.noConfusion)
  | psi k a =>
    exact logOm_mono_self rfl (fun e hc => Term.noConfusion hc)
      (fun _ hlt => le_of_psi_lt_phi_zero hlt) hx hy hya h
  | Z d =>
    exact logOm_mono_self rfl (fun e hc => Term.noConfusion hc)
      (fun _ hlt => le_of_Z_lt_phi_zero hlt) hx hy hya h
  | phi c d =>
    cases c with
    | zero => exact logOm_mono_pow hx hy hya h
    | M =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | omg _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | phi _ _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | psi _ _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | Z _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h
    | add _ _ =>
      exact logOm_mono_self rfl (fun e hc => by injection hc with h1 _; exact Term.noConfusion h1)
        (fun _ hlt => le_of_phi_lt_phi_zero (fun hc => Term.noConfusion hc) hlt) hx hy hya h

/-! `subAP w` — 頭部がちょうど `w` なら落とし、そうでなければ何もしない。 -/

theorem subAP_nil (w x : Term) (h : toList x = []) : subAP w x = zero := by
  show (match toList x with
        | [] => zero
        | p :: rest => if p == w then ofList rest else x) = _
  rw [h]

theorem subAP_cons (w x b : Term) (s : List Term) (h : toList x = b :: s) :
    subAP w x = if b == w then ofList s else x := by
  show (match toList x with
        | [] => zero
        | p :: rest => if p == w then ofList rest else x) = _
  rw [h]

theorem le_tail_of_le_add {u A B : Term} (h : le (add u A) (add u B) = true) :
    le A B = true := by
  by_cases heq : add u A = add u B
  · injection heq with _ h2
    rw [h2]
    exact Evidence.WF.le_self _
  · rcases (Bool.or_eq_true _ _).mp h with he | hl
    · exact absurd (eq_of_beq he) heq
    · rw [lt_add_add heq, if_pos rfl] at hl
      exact le_of_lt hl

/-- **`subAP w` は `{x : w ≤ x}` の上で単調。** 側条件を落とすと偽 (§65.7)。 -/
theorem subAP_mono_inT {w x y : Term} (hx : inT x = true) (hy : inT y = true)
    (hwx : lt x w = false) (h : le x y = true) :
    le (subAP w x) (subAP w y) = true := by
  obtain ⟨hcx, hdx⟩ := inT_toList x hx
  cases hxl : toList x with
  | nil => rw [subAP_nil w x hxl]; exact le_zero_left _
  | cons b s =>
    cases hyl : toList y with
    | nil =>
      exfalso
      have hyz : y = zero := toList_eq_nil y hyl
      rw [hyz] at h
      have hz : x = zero := by
        rcases (Bool.or_eq_true _ _).mp h with he | hl
        · exact eq_of_beq he
        · rw [lt_zero_right] at hl; exact Bool.noConfusion hl
      rw [hz] at hxl
      exact absurd (show b :: s = ([] : List Term) from hxl.symm) (List.cons_ne_nil b s)
    | cons c t =>
      rw [subAP_cons w x b s hxl, subAP_cons w y c t hyl]
      have hbc : le b c = true := hd_mono_inT hx hy hxl hyl h
      have hapb : b.isAP = true := inTL_isAP hx b (by rw [hxl]; exact List.Mem.head _)
      have hapc : c.isAP = true := inTL_isAP hy c (by rw [hyl]; exact List.Mem.head _)
      have hxe : x = ofList (b :: s) := by rw [← hxl, inT_ofList_toList x hx]
      have hye : y = ofList (c :: t) := by rw [← hyl, inT_ofList_toList y hy]
      rw [hxl] at hcx hdx
      obtain ⟨_, hcs⟩ := inTL_cons.mp hcx
      have hds := descL_tail hdx
      have his : inT (ofList s) = true := inT_ofList s hcs hds
      by_cases hcw : (c == w) = true
      · have hcw' : c = w := eq_of_beq hcw
        rw [if_pos hcw]
        by_cases hbw : (b == w) = true
        · rw [if_pos hbw]
          have hbw' : b = w := eq_of_beq hbw
          cases hs : s with
          | nil => exact le_zero_left _
          | cons a s' =>
            cases ht : t with
            | nil =>
              exfalso
              have hy' : y = w := by rw [hye, ht, hcw']; rfl
              have hx' : x = add w (ofList (a :: s')) := by rw [hxe, hs, hbw']; rfl
              have hlt : lt y x = true := by
                rw [hy', hx']
                exact lt_head_add (by rw [← hbw']; exact hapb) _
              rcases (Bool.or_eq_true _ _).mp h with he | hl
              · rw [eq_of_beq he, lt_irrefl] at hlt; exact Bool.noConfusion hlt
              · rw [lt_asymm_inT hx hy hl] at hlt; exact Bool.noConfusion hlt
            | cons d t' =>
              refine le_tail_of_le_add (u := w) ?_
              have hx' : x = add w (ofList (a :: s')) := by rw [hxe, hs, hbw']; rfl
              have hy' : y = add w (ofList (d :: t')) := by rw [hye, ht, hcw']; rfl
              rw [← hx', ← hy']
              exact h
        · exfalso
          have hbne : b ≠ w := fun hc => hbw (beq_of_eq hc)
          have hbltw : lt b w = true := by
            rw [← hcw']
            exact lt_of_le_of_ne hbc (by rw [hcw']; exact hbne)
          have hlt : lt x w = true := by
            rw [hxe, lt_ofList_nsum (by rw [← hcw']; exact hapc)]
            exact hbltw
          rw [hwx] at hlt
          exact Bool.noConfusion hlt
      · rw [if_neg hcw]
        by_cases hbw : (b == w) = true
        · rw [if_pos hbw]
          have hbw' : b = w := eq_of_beq hbw
          have hwc : lt w c = true := by
            rw [← hbw']
            exact lt_of_le_of_ne hbc (fun hc => hcw (beq_of_eq (hc.symm.trans hbw')))
          have hlsc : lt (ofList s) c = true := by
            cases hs : s with
            | nil => exact lt_zero_left (ne_zero_of_isAP hapc)
            | cons a s' =>
              rw [lt_ofList_nsum hapc]
              have haw : le a b = true := by
                rw [hs] at hdx
                exact (descL_cons.mp hdx).1
              have hia : inT a = true :=
                inTL_inT hx a (by rw [hxl, hs]; exact List.Mem.tail b (List.Mem.head _))
              exact lt_of_le_of_lt3 (inT_le_fragR a hia)
                (inT_le_fragR b (inTL_inT hx b (by rw [hxl]; exact List.Mem.head _)))
                (inT_le_fragR c (inTL_inT hy c (by rw [hyl]; exact List.Mem.head _)))
                haw (by rw [hbw']; exact hwc)
          refine le_of_lt (lt_of_lt_of_le3 (inT_le_fragR _ his)
            (inT_le_fragR c (inTL_inT hy c (by rw [hyl]; exact List.Mem.head _)))
            (inT_le_fragR y hy) hlsc (le_hd_self_inT hy hyl))
        · rw [if_neg hbw]
          exact h

/-! `plus e ·` の単調性。`e` の成分列の頭で場合分けし、尾に帰納する。 -/

theorem ofList_cons_ne_nil {a : Term} {L : List Term} (h : L ≠ []) :
    ofList (a :: L) = add a (ofList L) := by
  cases L with
  | nil => exact absurd rfl h
  | cons b t => rfl

theorem append_toList_ne_nil {L : List Term} {x x1 : Term} {X' : List Term}
    (hX : toList x = x1 :: X') : L ++ toList x ≠ [] := by
  rw [hX]
  cases L with
  | nil => exact List.cons_ne_nil x1 X'
  | cons a u => exact List.cons_ne_nil a (u ++ (x1 :: X'))

/-- 頭部が下なら和も下 (右辺の成分列が分かっているとき)。 -/
theorem lt_add_of_lt_hd {a A y y1 : Term} {Y' : List Term} (hy : inT y = true)
    (hY : toList y = y1 :: Y') (h : lt a y1 = true) : lt (add a A) y = true := by
  have hap : y1.isAP = true := inTL_isAP hy y1 (by rw [hY]; exact List.Mem.head _)
  have hye : y = ofList (y1 :: Y') := by rw [← hY, inT_ofList_toList y hy]
  rw [hye]
  cases Y' with
  | nil =>
    show lt (add a A) y1 = true
    rw [lt_add_nsum (ne_zero_of_isAP hap) (nsum_of_isAP hap)]
    exact h
  | cons d u =>
    show lt (add a A) (add y1 (ofList (d :: u))) = true
    refine lt_add_head ?_ h
    intro hc
    rw [hc, lt_irrefl] at h
    exact Bool.noConfusion h

theorem lt_of_hd_lt {e y e1 y1 : Term} {E' Y' : List Term} (he : inT e = true)
    (hy : inT y = true) (hE : toList e = e1 :: E') (hY : toList y = y1 :: Y')
    (h : lt e1 y1 = true) : lt e y = true := by
  have hee : e = ofList (e1 :: E') := by rw [← hE, inT_ofList_toList e he]
  have hi1 : inT e1 = true := inTL_inT he e1 (by rw [hE]; exact List.Mem.head _)
  have hj1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
  cases E' with
  | nil =>
    rw [show e = e1 from hee]
    exact lt_of_lt_of_le3 (inT_le_fragR e1 hi1) (inT_le_fragR y1 hj1)
      (inT_le_fragR y hy) h (le_hd_self_inT hy hY)
  | cons f F =>
    rw [hee]
    show lt (add e1 (ofList (f :: F))) y = true
    exact lt_add_of_lt_hd hy hY h

theorem plus_cons {e x e1 e' x1 : Term} {E' X' : List Term} (he : inT e = true)
    (hx : inT x = true) (hE : toList e = e1 :: E') (hE' : ofList E' = e')
    (hX : toList x = x1 :: X') :
    plus e x = if le x1 e1 then add e1 (plus e' x) else x := by
  obtain ⟨hce, hde⟩ := inT_toList e he
  rw [hE] at hce hde
  obtain ⟨⟨hap1, hi1⟩, hcE⟩ := inTL_cons.mp hce
  have htE : toList (ofList E') = E' := toList_ofList E' (fun z hz =>
    ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcE z hz)).1)
  have hix1 : inT x1 = true := inTL_inT hx x1 (by rw [hX]; exact List.Mem.head _)
  rw [plus_eq hX, hE, ← hE']
  by_cases hle : le x1 e1 = true
  · rw [if_pos hle, List.filter_cons_of_pos (by rw [hle]),
      plus_eq (s := ofList E') hX, htE]
    exact ofList_cons_ne_nil (append_toList_ne_nil hX)
  · rw [if_neg hle,
      filter_nil_of_head_inT hix1 e1 E' hi1 hcE hde (bool_false hle),
      List.nil_append]
    exact inT_ofList_toList x hx

theorem plus_mono_step {e e' e1 : Term} {E' : List Term} (he : inT e = true)
    (hE : toList e = e1 :: E') (hE' : ofList E' = e')
    (ih : ∀ x y, inT x = true → inT y = true → le x y = true →
        le (plus e' x) (plus e' y) = true) :
    ∀ (x y : Term), inT x = true → inT y = true → le x y = true →
      le (plus e x) (plus e y) = true := by
  intro x y hx hy h
  have hap1 : e1.isAP = true := inTL_isAP he e1 (by rw [hE]; exact List.Mem.head _)
  have hi1 : inT e1 = true := inTL_inT he e1 (by rw [hE]; exact List.Mem.head _)
  have hee : e = ofList (e1 :: E') := by rw [← hE, inT_ofList_toList e he]
  cases hX : toList x with
  | nil =>
    have hxz : x = zero := toList_eq_nil x hX
    subst hxz
    show le e (plus e y) = true
    cases hY : toList y with
    | nil =>
      have hyz : y = zero := toList_eq_nil y hY
      subst hyz
      exact Evidence.WF.le_self e
    | cons y1 Y' =>
      have hiy1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
      rw [plus_cons he hy hE hE' hY]
      by_cases hle : le y1 e1 = true
      · rw [if_pos hle]
        cases hEc : E' with
        | nil =>
          rw [hEc] at hee
          rw [show e = e1 from hee]
          exact le_of_lt (lt_head_add hap1 _)
        | cons f F =>
          rw [hEc] at hee hE'
          have hee2 : e = add e1 e' := by rw [hee, ← hE']; rfl
          rw [hee2]
          refine le_add_tail ?_
          exact ih zero y inT_zero hy (le_zero_left y)
      · rw [if_neg hle]
        refine le_of_lt (lt_of_hd_lt he hy hE hY ?_)
        exact lt_of_not_le_inT hiy1 hi1 (bool_false hle)
  | cons x1 X' =>
    have hix1 : inT x1 = true := inTL_inT hx x1 (by rw [hX]; exact List.Mem.head _)
    rw [plus_cons he hx hE hE' hX]
    cases hY : toList y with
    | nil =>
      exfalso
      have hyz : y = zero := toList_eq_nil y hY
      rw [hyz] at h
      have hz : x = zero := by
        rcases (Bool.or_eq_true _ _).mp h with hq | hl
        · exact eq_of_beq hq
        · rw [lt_zero_right] at hl; exact Bool.noConfusion hl
      rw [hz] at hX
      exact absurd (show x1 :: X' = ([] : List Term) from hX.symm) (List.cons_ne_nil x1 X')
    | cons y1 Y' =>
      have hiy1 : inT y1 = true := inTL_inT hy y1 (by rw [hY]; exact List.Mem.head _)
      rw [plus_cons he hy hE hE' hY]
      have hxy1 : le x1 y1 = true := hd_mono_inT hx hy hX hY h
      by_cases hlx : le x1 e1 = true
      · rw [if_pos hlx]
        by_cases hly : le y1 e1 = true
        · rw [if_pos hly]
          exact le_add_tail (ih x y hx hy h)
        · rw [if_neg hly]
          refine le_of_lt (lt_add_of_lt_hd hy hY ?_)
          exact lt_of_not_le_inT hiy1 hi1 (bool_false hly)
      · have hly : ¬ (le y1 e1 = true) := by
          intro hc
          exact hlx (le_trans_inT hix1 hiy1 hi1 hxy1 hc)
        rw [if_neg hlx, if_neg hly]
        exact h

/-- **`plus e ·` は単調。** 側条件なし。 -/
theorem plus_mono_right_inT : ∀ (e : Term), inT e = true → ∀ (x y : Term), inT x = true →
    inT y = true → le x y = true → le (plus e x) (plus e y) = true := by
  have hzero : ∀ (x y : Term), inT x = true → inT y = true → le x y = true →
      le (plus zero x) (plus zero y) = true := by
    intro x y hx hy h
    rw [plus_zero_left_inT hx, plus_zero_left_inT hy]
    exact h
  intro e
  induction e with
  | zero => intro _; exact hzero
  | M => intro he; exact plus_mono_step he rfl rfl hzero
  | omg _ _ => intro he; exact plus_mono_step he rfl rfl hzero
  | phi _ _ _ _ => intro he; exact plus_mono_step he rfl rfl hzero
  | psi _ _ _ _ => intro he; exact plus_mono_step he rfl rfl hzero
  | Z _ _ => intro he; exact plus_mono_step he rfl rfl hzero
  | add u v _ ihv =>
    intro he
    obtain ⟨_, _, hiv, _⟩ := inT_add he
    exact plus_mono_step he rfl (inT_ofList_toList v hiv) (ihv hiv)

/-- **SC の一段。** `w` が強臨界で `w ≤ p` (`p` は加法主要) なら `w ≤ logOm p`。
    これが (G1) の側条件が `w ∈ SC` でなければならない理由。`w = p = 1` で破れる。 -/
theorem lt_logOm_of_sc {w p : Term} (hsc : w.isSC = true) (hw : inT w = true)
    (hap : p.isAP = true) (hp : inT p = true) (h : lt p w = false) :
    lt (logOm p) w = false := by
  have hlew : le w p = true := le_of_not_lt3 (inT_le_fragR p hp) (inT_le_fragR w hw) h
  have hkey : le w (logOm p) = true := by
    cases p with
    | zero => exact Bool.noConfusion hap
    | add _ _ => exact Bool.noConfusion hap
    | M => exact hlew
    | omg _ => exact hlew
    | psi _ _ => exact hlew
    | Z _ => exact hlew
    | phi c d =>
      cases c with
      | zero =>
        refine le_logOm_phi_zero_of_le hw (inT_phi4 hp).2.1 ?_
        cases w with
        | zero => exact Bool.noConfusion hsc
        | omg _ => exact Bool.noConfusion hsc
        | phi _ _ => exact Bool.noConfusion hsc
        | add _ _ => exact Bool.noConfusion hsc
        | M =>
          exfalso
          rw [show le (M : Term) (phi zero d) = false from by
            show ((M == phi zero d) || lt M (phi zero d)) = false
            rw [show ((M : Term) == phi zero d) = false from rfl,
              show lt (M : Term) (phi zero d) = false from by
                rw [lt_eq_ltF_succ]; exact ltF_succ_M_phi _ _ _]
            rfl] at hlew
          exact Bool.noConfusion hlew
        | psi k a =>
          exact le_of_psi_lt_phi_zero
            (lt_of_le_of_ne hlew (by intro hc; exact Term.noConfusion hc))
        | Z e =>
          exact le_of_Z_lt_phi_zero
            (lt_of_le_of_ne hlew (by intro hc; exact Term.noConfusion hc))
      | M => exact hlew
      | omg _ => exact hlew
      | phi _ _ => exact hlew
      | psi _ _ => exact hlew
      | Z _ => exact hlew
      | add _ _ => exact hlew
  rcases (Bool.or_eq_true _ _).mp hkey with he | hl
  · rw [← eq_of_beq he, lt_irrefl]
  · exact lt_asymm_inT hw (inT_logOm hp) hl

end

/-! ### §65.5 (G1) を直した形と、(G2) そのもの

`DivDescSC` は §64 の `DivDescInT` に `w ∈ SC` を 1 つ足したもの。足さないと偽で、反例は
§65.7 に凍結してある。`MulDescInT` は §64 の定義そのままで、直しは要らない。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (logOm subAP divAP mulL)

/-- **(G1) を直した形。** §64 の `DivDescInT` に `w.isSC` を足したもの。 -/
def DivDescSC : Prop := ∀ (w : Term) (l : List Term), inT w = true → w.isSC = true →
  inTL l = true → descL l = true → (∀ q ∈ l, lt q w = false) →
  descL (l.map (divAP w)) = true

/-- **(G1) は偽。** §64 の `DivDescInT` の反証 — `w = ω`, `l = [ω^ω, ω]`。 -/
theorem not_divDescInT : ¬ DivDescInT := by
  intro H
  have h := H omega [phi zero omega, omega] rfl rfl rfl
    (by intro q hq
        rcases List.mem_cons.mp hq with h1 | h1
        · rw [h1]; rfl
        · rw [List.mem_singleton.mp h1]; rfl)
  exact Bool.noConfusion (h.symm.trans
    (show descL ([phi zero omega, omega].map (divAP omega)) = false from rfl))

/-- **(G1) 完了。** `logOm` の単調性 → SC の一段 → `subAP` の単調性 → `ω^·` の単調性。 -/
theorem divDescSC : DivDescSC := by
  intro w l hw hsc hcl hdl hge
  refine descL_map_mono (divAP w)
    (fun p => p.isAP = true ∧ inT p = true ∧ lt p w = false) ?_ l ?_ hdl
  · intro a b ha hb hba
    obtain ⟨hapa, hia, _⟩ := ha
    obtain ⟨hapb, hib, hwb⟩ := hb
    show le (omegaNF (subAP w (logOm b))) (omegaNF (subAP w (logOm a))) = true
    refine omegaNF_mono_inT (inT_subAP (inT_logOm hib)) (inT_subAP (inT_logOm hia)) ?_
    refine subAP_mono_inT (inT_logOm hib) (inT_logOm hia)
      (lt_logOm_of_sc hsc hw hapb hib hwb) ?_
    exact logOm_mono_inT hapb hapa hib hia hba
  · intro x hx
    exact ⟨((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcl x hx)).1,
           ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hcl x hx)).2, hge x hx⟩

/-- **(G2) 完了。** §64 の `MulDescInT` そのまま — 側条件は要らない。 -/
theorem mulDescInT : MulDescInT := by
  intro e y he hy
  obtain ⟨hc, hd⟩ := inT_toList y hy
  refine descL_map_mono (fun p => omegaNF (plus e (logOm p)))
    (fun p => p.isAP = true ∧ inT p = true) ?_ (toList y) ?_ hd
  · intro a b ha hb hba
    obtain ⟨hapa, hia⟩ := ha
    obtain ⟨hapb, hib⟩ := hb
    refine omegaNF_mono_inT (inT_plus he (inT_logOm hib)) (inT_plus he (inT_logOm hia)) ?_
    exact plus_mono_right_inT e he _ _ (inT_logOm hib) (inT_logOm hia)
      (logOm_mono_inT hapb hapa hib hia hba)
  · intro x hx
    exact ⟨inTL_isAP hy x hx, inTL_inT hy x hx⟩

end

/-! ### §65.6 消費者 — `wcnf`・`collapse`・`dict` を直した仮説の上で

§64.4 の `wcnf_spec` と §64.5 の `inT_collapse` / `inT_dict` / `collapseInT_of_gaps` は
**偽である `DivDescInT` を仮説に取っている**ので、そのままでは使えない。ここでは同じ証明を
`DivDescSC` に対して引き直す。呼び出し側の底はいつも `reg (u+1) = Z u` で、`isSC` は `rfl`。

§64.3 の `inT_mulL` / `ltM_mulL` と §64.5 の `inT_idxOf` / `stepF_inv` / `fold_inv` は
`MulDescInT` しか取らないので、そのまま `mulDescInT` を渡して再利用する。 -/

section
open Trans.Recal (bplus)
open TM TM.Term
open Evidence.WF
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)

theorem isSC_reg_succ (u : Nat) : (reg (u + 1)).isSC = true := rfl

theorem inT_wA_sc {w p : Term} (hw : inT w = true) (hsc : w.isSC = true)
    (hp : inT p = true) : inT (wA w p) = true := by
  obtain ⟨hc, hd⟩ := inT_toList _ (inT_logOm hp)
  refine inT_ofList _ ?_
    (divDescSC w _ hw hsc (inTL_filter _ hc) (descL_filter_inT _ hc hd _) ?_)
  · show (List.map (divAP w) _).all _ = true
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨q, hq, hxe⟩ := List.mem_map.mp hx
    rw [← hxe]
    show ((divAP w q).isAP && inT (divAP w q)) = true
    rw [isAP_divAP, inT_divAP (inTL_inT (inT_logOm hp) q (List.mem_filter.mp hq).1)]
    rfl
  · intro q hq
    have hq2 := (List.mem_filter.mp hq).2
    cases hlq : lt q w with
    | false => rfl
    | true => rw [hlq] at hq2; exact Bool.noConfusion hq2

/-- **`wcnf` は 𝔗(M) の中に留まる** — 底が強臨界なら。§64.4 の `wcnf_spec` の直した版。 -/
theorem wcnf_spec_sc {w : Term} (hw : inT w = true) (hsc : w.isSC = true) :
    ∀ (L : List Term), inTL L = true → descL L = true → (∀ x ∈ L, lt x M = true) →
      PairOK (wcnf w L) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _
    exact ⟨⟨inT_zero, lt_zero_M⟩, by intro ac hac; cases hac⟩
  | cons p rest ih =>
    intro hc hd hm
    obtain ⟨⟨hap, hip⟩, hcr⟩ := inTL_cons.mp hc
    have hdr := descL_tail hd
    have hmr : ∀ x ∈ rest, lt x M = true := fun x hx => hm x (List.Mem.tail p hx)
    have hlpM : lt p M = true := hm p (List.Mem.head _)
    have IH := ih hcr hdr hmr
    by_cases hlp : lt p w = true
    · rw [wcnf_cons_lt hlp]
      exact ⟨⟨inT_ofList _ hc hd, lt_ofList_M _ hm⟩, by intro ac hac; cases hac⟩
    · have hlp' : lt p w = false := bool_false hlp
      have hA := inT_wA_sc (w := w) hw hsc hip
      have hAM := ltM_wA (w := w) hip hlpM
      have hC := inT_wC (w := w) hip
      have hCM := ltM_wC (w := w) hip hlpM
      rw [wcnf_cons_ge hlp']
      cases hr : wcnf w rest with
      | mk fst snd =>
        rw [hr] at IH
        obtain ⟨⟨hs1, hs2⟩, hall⟩ := IH
        cases fst with
        | nil =>
          refine ⟨⟨hs1, hs2⟩, ?_⟩
          intro ac hac
          rw [List.mem_singleton.mp hac]
          exact ⟨hA, hAM, hC, hCM⟩
        | cons ac0 ps =>
          cases ac0 with
          | mk a' c' =>
            have hac0 := hall (a', c') (List.Mem.head _)
            show PairOK (if (wA w p == a') = true
              then ((wA w p, plus (wC w p) c') :: ps, snd)
              else ((wA w p, wC w p) :: (a', c') :: ps, snd))
            by_cases heq : (wA w p == a') = true
            · rw [if_pos heq]
              refine ⟨⟨hs1, hs2⟩, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with hq | hq
              · rw [hq]
                exact ⟨hA, hAM, inT_plus hC hac0.2.2.1,
                  lt_plus_M hC hac0.2.2.1 hCM hac0.2.2.2⟩
              · exact hall ac (List.Mem.tail _ hq)
            · rw [if_neg heq]
              refine ⟨⟨hs1, hs2⟩, ?_⟩
              intro ac hac
              rcases List.mem_cons.mp hac with hq | hq
              · rw [hq]; exact ⟨hA, hAM, hC, hCM⟩
              · exact hall ac hq

/-- **`collapse` は 𝔗(M) に落ちる** — (G3) だけを仮定して。§64.5 の `inT_collapse` から
    (G1)(G2) の仮説が消えた形。 -/
theorem inT_collapse_gap3 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (Hp : PsiIdxOK u x) :
    inT (collapse u x) = true ∧ lt (collapse u x) M = true := by
  obtain ⟨hc, hd⟩ := inT_toList x hx
  obtain ⟨⟨h21, h22⟩, hallOK⟩ :=
    wcnf_spec_sc (inT_reg (u+1)) (isSC_reg_succ u) (toList x) hc hd (ltM_toList x hx hlx)
  have hinit : StInv ((none : Option Term), (none : Option Term)) := by
    constructor
    · intro i0 hq; cases hq
    · intro v hq; cases hq
  have hst := fold_inv mulDescInT (inT_reg (u+1)) (ltM_reg (u+1)) (inT_baseOf u) (ltM_baseOf u)
    (wcnf (reg (u+1)) (toList x)).1 (none, none) hinit hallOK Hp
  have hv : inT (((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2.getD zero) = true ∧
      lt (((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2.getD zero) M = true := by
    cases hg : ((wcnf (reg (u+1)) (toList x)).1.foldl
        (init := ((none : Option Term), (none : Option Term)))
        (stepF (reg (u+1)) (baseOf u))).2 with
    | none => exact ⟨inT_zero, lt_zero_M⟩
    | some v => exact hst.2 v hg
  rw [collapse_eq]
  have harg : inT (plus (reg u) (plus _ (wcnf (reg (u+1)) (toList x)).2)) = true :=
    inT_plus (inT_reg u) (inT_plus hv.1 h21)
  have hlarg : lt (plus (reg u) (plus _ (wcnf (reg (u+1)) (toList x)).2)) M = true :=
    lt_plus_M (inT_reg u) (inT_plus hv.1 h21) (ltM_reg u)
      (lt_plus_M hv.1 h21 hv.2 h22)
  exact ⟨inT_omegaNF harg, ltM_omegaNF harg hlarg⟩

/-- 強臨界枝が一度も点火しない断片では、もう仮説はひとつも要らない。 -/
theorem inT_collapse_noSC_gap3 (u : Nat) (x : Term) (hx : inT x = true) (hlx : lt x M = true)
    (h : ∀ ac ∈ (wcnf (reg (u+1)) (toList x)).1, le (reg (u+1)) ac.1 = false) :
    inT (collapse u x) = true :=
  (inT_collapse_gap3 u x hx hlx (psiIdxOK_of_noSC u x h)).1

/-- `dict` の像は 𝔗(M) の中で `M` の下 — (G3) だけを仮定して。 -/
theorem inT_dict_gap3 (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :
    ∀ a : BT, inT (dict a) = true ∧ lt (dict a) M = true
  | .zero => ⟨inT_zero, lt_zero_M⟩
  | .D u a => by
    have ih := inT_dict_gap3 Hp a
    exact inT_collapse_gap3 u (dict a) ih.1 ih.2 (Hp u a)
  | .sum a b => by
    have iha := inT_dict_gap3 Hp a
    have ihb := inT_dict_gap3 Hp b
    exact ⟨inT_plus iha.1 ihb.1, lt_plus_M iha.1 ihb.1 iha.2 ihb.2⟩

/-- **§65 の主定理。** §63 の `CollapseInT` は (G3) だけに還元される。 -/
theorem collapseInT_of_gap3 (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) : CollapseInT :=
  fun u a => (inT_dict_gap3 Hp (BT.D u a)).1

/-- **消費者を通す。** §63 の `hsuccS_supply` — `certIn_region` の 2 番目の供給 — が
    (G3) だけで開く。 -/
theorem hsuccS_supply_of_gap3 (Hp : ∀ (u : Nat) (a : BT), PsiIdxOK u (dict a)) :
    ∀ (S : BMS.Matrix) (v : TM.Term), RegS S → ValS S v → BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u TM.Term.one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, ValS (BMS.expand S n) u :=
  hsuccS_supply (collapseInT_of_gap3 Hp)

end

/-! ### §65.7 測定 (凍結)

否定的なものから。母集団は `ofNat` を種に入れてある — §64 の 2 つの母集団がどちらも
`ω^n` を作れず、しかも肯定側の掃引が `l` を「母集団の項 `y` の `toList`」に限っていたので、
(G1) の反例が 82373 + 2324 組すべてをすり抜けていた。 -/

section
open TM TM.Term
open Evidence.WF
open Trans.Recal
open Trans.Dict (wcnf divAP logOm subAP mulL sub1 reg collapse dict)
open Trans.Dict (BT)

/-! **否定 1 — (G1) `DivDescInT` は偽。** `w = ω`, `l = [ω^ω, ω]`、次数和 17。 -/

#guard inT omega && inT (phi zero omega)
#guard omega.isAP && (phi zero omega).isAP
#guard descL [phi zero omega, omega]
#guard !(lt (phi zero omega) omega) && !(lt omega omega)
#guard !(descL ([phi zero omega, omega].map (divAP omega)))
#guard ([phi zero omega, omega].map (divAP omega)) == [one, omega]
#guard omega.deg + (phi zero omega).deg + omega.deg == 17
--   `w = ω` は SC ではない。これが唯一の逃げ道である。
#guard !(omega.isSC)
--   `l` は正真正銘 𝔗(M) の項の成分列 — 命題の一般性の artefact ではない。
#guard inT (add (phi zero omega) omega)
#guard TM.Term.toList (add (phi zero omega) omega) == [phi zero omega, omega]
--   §64 の判定器でも同じ。
#guard !(divDescb omega [phi zero omega, omega])
--   壊れているのは `w ≤ p` から `w ≤ logOm p` への一段。
#guard !(lt omega omega) && lt (logOm omega) omega
#guard logOm omega == one

/-! **否定 2 — `logOm` の単調性は加法主要を落とすと偽。** 最小は `Ω ⊕ Ω ≤ ω^Ω`、次数和 9。 -/

#guard le (add (Z zero) (Z zero)) (phi zero (Z zero))
#guard !(le (logOm (add (Z zero) (Z zero))) (logOm (phi zero (Z zero))))
#guard (add (Z zero) (Z zero)).deg + (phi zero (Z zero)).deg == 9
#guard !((add (Z zero) (Z zero)).isAP)

/-! **否定 3 — `subAP` の単調性は `w ≤ x` を落とすと偽。** 最小は `w = M`, `x = Ω`, `y = M`。 -/

#guard le (Z zero) (M : Term)
#guard !(le (subAP M (Z zero)) (subAP M M))
#guard (M : Term).deg + (Z zero).deg + (M : Term).deg == 4
#guard lt (Z zero) M          -- `w ≤ x` が破れている

/-! **否定 4 — SC の一段は SC を落とすと偽。** `w = p = 1`。 -/

#guard !(lt one one) && lt (logOm one) one
#guard !((one : Term).isSC)

/-! **否定 5 — `z < ω^z` は `z < M` を要る。** `z = M` で偽。 -/

#guard !(lt M (phi zero M))
#guard !(lt (M : Term) M)

/-! 肯定。母集団は `ofNat` 入りの閉包を 2 段。 -/

private def b65 : List Term :=
  [zero, one, ofNat 2, ofNat 3, omega, Z zero, M, psi (Z zero) zero, phi one zero]
private def stp65 (l : List Term) : List Term :=
  l ++ (l.flatMap fun a => l.map fun b => add a b)
    ++ (l.flatMap fun a => l.map fun b => phi a b)
    ++ (l.map fun a => omegaNF a)
    ++ (l.map fun a => Z a)
    ++ (l.map fun a => omg a)
private def raw65 : List Term := (stp65 b65).eraseDups
private def C65 : List Term := raw65.filter fun x => inT x
private def C65ap : List Term := C65.filter fun x => x.isAP
private def D65 : List Term := ((stp65 (C65.take 22)).eraseDups.filter fun x => inT x).take 120
private def D65ap : List Term := D65.filter fun x => x.isAP

#guard raw65.length == 183
#guard C65.length == 109
#guard C65ap.length == 75
#guard D65.length == 120
#guard D65ap.length == 45
#guard (D65.map fun x => x.deg).foldl (fun a b => if a < b then b else a) 0 == 23

/-! 肯定 1. `ω^·` の 3 分岐 (`omegaNF_eq_gen`) — `inT` でない項も含めて 0 失敗。 -/

private def omEq65 (x : Term) : Bool :=
  omegaNF x ==
    (if lt M x then omg x else if TM.Term.isFP zero x then x else phi zero (dnArg x))
#guard (raw65.filter fun x => !(omEq65 x)).length == 0
#guard (D65.filter fun x => !(omEq65 x)).length == 0

/-! 肯定 2. `logOm` の単調性 — 加法主要に限れば 0 失敗、落とすと 33 失敗。 -/

#guard (C65ap.flatMap fun x => C65ap.filter fun y =>
    le x y && !(le (logOm x) (logOm y))).length == 0
#guard (D65ap.flatMap fun x => D65ap.filter fun y =>
    le x y && !(le (logOm x) (logOm y))).length == 0
#guard (C65.flatMap fun x => C65.filter fun y =>
    le x y && !(le (logOm x) (logOm y))).length == 33

/-! 肯定 3. `ω^·` の単調性 (非狭義) — 0 失敗。 -/

#guard (C65.flatMap fun x => C65.filter fun y =>
    le x y && !(le (omegaNF x) (omegaNF y))).length == 0
#guard (D65.flatMap fun x => D65.filter fun y =>
    le x y && !(le (omegaNF x) (omegaNF y))).length == 0

/-! 肯定 4. D1 と D2 — 0 失敗。D3 は使っていないので測っていない。 -/

#guard (C65.filter fun x => !(le (dnArg x) x)).length == 0
#guard (C65.flatMap fun x => C65.filter fun y => lt x y && !(le x (dnArg y))).length == 0
#guard (D65.filter fun x => !(le (dnArg x) x)).length == 0
#guard (D65.flatMap fun x => D65.filter fun y => lt x y && !(le x (dnArg y))).length == 0

/-! 肯定 5. `plus e ·` の単調性 — 側条件なしで 0 失敗 (109³ 組)。 -/

#guard (C65.flatMap fun e => C65.flatMap fun x => C65.filter fun y =>
    le x y && !(le (plus e x) (plus e y))).length == 0

/-! 肯定 6. `subAP w` の単調性 — `w ≤ x` があれば 0 失敗、無いと 2073 失敗。
    **`w ∈ SC` は `subAP` には要らない** (証明も使っていない)。 -/

#guard (C65.flatMap fun w => C65.flatMap fun x => C65.filter fun y =>
    !(lt x w) && le x y && !(le (subAP w x) (subAP w y))).length == 0
#guard (D65.flatMap fun w => D65.flatMap fun x => D65.filter fun y =>
    !(lt x w) && !(lt y w) && le x y && !(le (subAP w x) (subAP w y))).length == 0
#guard (C65.flatMap fun w => C65.flatMap fun x => C65.filter fun y =>
    w.isSC && le x y && !(le (subAP w x) (subAP w y))).length == 2073

/-! 肯定 7. SC の一段 — `w ∈ SC` なら 0 失敗、落とすと 46 失敗。 -/

#guard (C65.flatMap fun w => C65ap.filter fun p =>
    w.isSC && !(lt p w) && (lt (logOm p) w)).length == 0
#guard (D65.flatMap fun w => D65ap.filter fun p =>
    w.isSC && !(lt p w) && (lt (logOm p) w)).length == 0
#guard (C65.flatMap fun w => C65ap.filter fun p =>
    !(lt p w) && (lt (logOm p) w)).length == 46

/-! 肯定 8. (G1) を直した形 — 0 失敗。C65 で 1270 組、D65 で 403 組。 -/

#guard (C65.flatMap fun w => C65ap.flatMap fun p => C65ap.filter fun p' =>
    w.isSC && le p' p && !(lt p w) && !(lt p' w)
      && !(descL [divAP w p, divAP w p'])).length == 0
#guard (C65.flatMap fun w => C65ap.flatMap fun p => C65ap.filter fun p' =>
    w.isSC && le p' p && !(lt p w) && !(lt p' w)).length == 1270
#guard (D65.flatMap fun w => D65ap.flatMap fun p => D65ap.filter fun p' =>
    w.isSC && le p' p && !(lt p w) && !(lt p' w)
      && !(descL [divAP w p, divAP w p'])).length == 0
#guard (D65.flatMap fun w => D65ap.flatMap fun p => D65ap.filter fun p' =>
    w.isSC && le p' p && !(lt p w) && !(lt p' w)).length == 403

/-! 肯定 9. (G2) — 0 失敗。 -/

#guard (C65.flatMap fun e => C65.filter fun y => !(mulDescb e y)).length == 0
#guard (D65.flatMap fun e => D65.filter fun y => !(mulDescb e y)).length == 0

/-! 肯定 10. 領域そのもの。§64.6 肯定 6 を、(G1)(G2) が定理になった今の形で取り直す。 -/

#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.length == 443
#guard ((popNFB 3 6).flatMap fun t => (bVal t).toL).eraseDups.all fun a =>
  TM.Term.inT (Trans.Dict.dict a)


end

/-! ### §65.8 公理 -/

section
open Trans.Recal (bplus)
open Trans.Dict (BT dict)
open TM TM.Term
open Evidence.WF

end

end Evidence.Region
