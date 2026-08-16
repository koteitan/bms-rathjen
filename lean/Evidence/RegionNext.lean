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

end Evidence.Region
