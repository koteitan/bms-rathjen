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

end Evidence.Region
