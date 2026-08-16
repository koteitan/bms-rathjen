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

/-! ## §6 THE NEAR CASE — the bad root is the last node's PARENT

§3.2's rule sends the iteration to the nearest ancestor of lower level.  When that ancestor
is the last node's own parent, the depth gap is 1 and the two frame lemmas of §5 apply
directly; `nearB` is exactly that condition, read down the last chain.

MEASURED: 645 of the 877 matrices of §3.5's population are near, and 40 of the 52 rows.
The other 232 need a frame with a depth gap `e ≥ 2` — ζ₀ `(0,0)(1,1)(2,1)` is the smallest,
where the last node's parent is a `ψ₁` and the bad root is the `ψ₀` above it.  That is the
one thing this section does NOT prove, and it is the next piece of work: `frame_parent0`
places the row-0 bad root at the block's own root, which is true only when the last column
sits at depth `d + 1`.

Everything else — the value, the normal form, the limit clauses — comes after. -/

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

/-- 悪い根が最後の節の**親**であること (深さの差が 1)。 -/
def nearB (v : Nat) : B → Bool
  | .nil => false
  | .nd w _ .nil => (w == 0) || decide (v < w)
  | .nd w _ c => nearB w c

theorem nearB_low : ∀ (a : B) (v : Nat), nearB v a = true →
    lastLvl a = 0 ∨ (decide (v < lastLvl a) || hasLowAnc (lastLvl a) a) = true := by
  intro a
  induction a with
  | nil => intro v h; exact absurd h (by simp [nearB])
  | nd w b c _ ihc =>
    intro v h
    cases c with
    | nil =>
      cases w with
      | zero => exact Or.inl rfl
      | succ k =>
        refine Or.inr ?_
        have hv : ((k + 1 == 0) || decide (v < k + 1)) = true := h
        simp at hv
        show (decide (v < k + 1) || hasLowAnc (k + 1) (.nd (k+1) b .nil)) = true
        rw [show decide (v < k + 1) = true from by simp; omega]
        rfl
    | nd u b' c' =>
      have h' : nearB w (.nd u b' c') = true := h
      rcases ihc w h' with hz | hl
      · exact Or.inl hz
      · refine Or.inr ?_
        show (decide (v < lastLvl (B.nd u b' c'))
          || (decide (w < lastLvl (B.nd u b' c'))
              || hasLowAnc (lastLvl (B.nd u b' c')) (.nd u b' c'))) = true
        rw [hl]
        exact Bool.or_true _

/-- **近い場合の展開の等式。** 悪い根が最後の節の親なら、展開は `stepBv` で書ける。 -/
theorem expand_blkB : ∀ (a : B) (v : Nat), nearB v a = true →
    ∀ (P : Matrix) (d n : Nat),
      expand? (P ++ matB (.nd v .nil a) d) n = some (P ++ matB (stepBv v .nil a n) d) := by
  intro a
  induction a with
  | nil => intro v h; exact absurd h (by simp [nearB])
  | nd w b c _ ihc =>
    intro v h P d n
    cases c with
    | nil =>
      cases w with
      | zero =>
        rw [expand_prinB_succ v b P d n]
        refine congrArg some (congrArg (P ++ ·) (congrArg (matB · d) ?_))
        show _ = if lastLvl (B.nd 0 b .nil) == 0 then repB (.nd v .nil (.nd 0 b .nil)) n else _
        rw [if_pos (show (lastLvl (B.nd 0 b (B.nil)) == 0) = true from rfl)]
        show _ = appB .nil (repNode v b n)
        rw [appB_nil]
      | succ k =>
        have hvw : v < k + 1 := by
          have : ((k + 1 == 0) || decide (v < k + 1)) = true := h
          simp at this
          omega
        rw [expand_prinB_tower v (k + 1) hvw b P d n]
        refine congrArg some (congrArg (P ++ ·) (congrArg (matB · d) ?_))
        show _ = if lastLvl (B.nd (k+1) b .nil) == 0 then _
                 else rwB (lastLvl (B.nd (k+1) b .nil)) n (.nd v .nil (.nd (k+1) b .nil))
        rw [if_neg (show ¬((lastLvl (B.nd (k+1) b (B.nil)) == 0) = true) from by simp [lastLvl])]
        show _ = (if hasLowAnc (k+1) (.nd (k+1) b .nil) then _
                  else if v < k + 1 then appB .nil (iterD v (.nd (k+1) b .nil) n) else _)
        rw [if_neg (show ¬(hasLowAnc (k+1) (B.nd (k+1) b (B.nil)) = true) from by simp [hasLowAnc]),
          if_pos hvw, appB_nil, iterD_eq v (k+1) b n]
    | nd u b' c' =>
      have h' : nearB w (.nd u b' c') = true := h
      have hstep := ihc w h'
      rw [expand_prinB_deep v w b (.nd u b' c') (stepBv w .nil (.nd u b' c') n) n
        (fun P' d' => hstep P' d' n) P d]
      refine congrArg some (congrArg (P ++ ·) (congrArg (matB · d) ?_))
      show B.nd v .nil (appB b (stepBv w .nil (.nd u b' c') n))
        = if lastLvl (B.nd w b (.nd u b' c')) == 0 then
            repB (.nd v .nil (.nd w b (.nd u b' c'))) n
          else rwB (lastLvl (B.nd w b (.nd u b' c'))) n (.nd v .nil (.nd w b (.nd u b' c')))
      rw [← stepBv_prefix w b u b' c' n]
      by_cases h0 : (lastLvl (B.nd w b (.nd u b' c')) == 0) = true
      · rw [if_pos h0,
          show repB (B.nd v .nil (.nd w b (.nd u b' c'))) n
            = B.nd v .nil (repB (.nd w b (.nd u b' c')) n) from by cases w <;> rfl]
        refine congrArg (B.nd v .nil) ?_
        show (if lastLvl (B.nd u b' c') == 0 then repB (.nd w b (.nd u b' c')) n else _) = _
        rw [if_pos (show (lastLvl (B.nd u b' c') == 0) = true from h0)]
      · rw [if_neg h0]
        have hla : hasLowAnc (lastLvl (B.nd w b (.nd u b' c'))) (.nd w b (.nd u b' c')) = true := by
          rcases nearB_low (.nd u b' c') w h' with hz | hl
          · exact absurd (show (lastLvl (B.nd w b (.nd u b' c')) == 0) = true from by
              show (lastLvl (B.nd u b' c') == 0) = true; rw [hz]; rfl) h0
          · exact hl
        rw [show rwB (lastLvl (B.nd w b (.nd u b' c'))) n (B.nd v .nil (.nd w b (.nd u b' c')))
              = B.nd v .nil (rwB (lastLvl (B.nd w b (.nd u b' c'))) n (.nd w b (.nd u b' c'))) from by
            show (if hasLowAnc (lastLvl (B.nd w b (.nd u b' c'))) (.nd w b (.nd u b' c')) then
                    B.nd v .nil (rwB (lastLvl (B.nd w b (.nd u b' c'))) n (.nd w b (.nd u b' c')))
                  else _) = _
            rw [if_pos hla]]
        refine congrArg (B.nd v .nil) ?_
        show (if lastLvl (B.nd u b' c') == 0 then _
              else rwB (lastLvl (B.nd u b' c')) n (.nd w b (.nd u b' c'))) = _
        rw [if_neg (show ¬((lastLvl (B.nd u b' c') == 0) = true) from h0)]
        rfl

/-- 最上位の加数は `ψ₀` の節でなければならない (値が `Ω` 未満)。 -/
def topOKB : B → Bool
  | .nil => true
  | .nd v r _ => (v == 0) && topOKB r

/-- 悪い根が最後の節の親であること、最上位から見て。 -/
def nearTopB : B → Bool
  | .nil => false
  | .nd _ _ .nil => true
  | .nd v _ a => nearB v a

/-- **一般化した領域は展開で閉じている — 近い場合。** -/
theorem expand_matB : ∀ (t : B), topOKB t = true → nearTopB t = true → ∀ (n : Nat),
    expand? (matB t 0) n = some (matB (fsB t n) 0) := by
  intro t
  cases t with
  | nil => intro _ h; exact absurd h (by simp [nearTopB])
  | nd v r a =>
    cases a with
    | nil =>
      intro htop _ n
      have hv : v = 0 := by
        have : ((v == 0) && topOKB r) = true := htop
        simp at this
        exact this.1
      subst hv
      show expand? (matB r 0 ++ [[0, 0]]) n = some (matB (fsB (.nd 0 r .nil) n) 0)
      rw [expand?_succ _ [0, 0] (by simp) (by rw [lnz_pair]; simp) n]
      show some (matB r 0 ++ [[0, 0]]).dropLast = some (matB r 0)
      simp
    | nd w b c =>
      intro _ hnear n
      show expand? (matB r 0 ++ matB (.nd v .nil (.nd w b c)) 0) n = _
      rw [expand_blkB (.nd w b c) v hnear (matB r 0) 0 n,
        ← matB_app (stepBv v .nil (.nd w b c) n) r 0,
        ← stepBv_prefix v r w b c n, ← fsB_eq_stepBv v r w b c n]

/-! ### §6.1 HOW MUCH THE NEAR CASE COVERS -/

#guard (popB.filter fun S =>
  match decodeB S with | none => true | some t => nearTopB t).length == 645
#guard (wideRows.filter fun M =>
  match decodeB M with | none => true | some t => nearTopB t).length == 40
-- 残る 232 個は深さの差が 2 以上。最小は ζ₀。
#guard (popB.filter fun S =>
  match decodeB S with | none => false | some t => !(nearTopB t)).length == 232
#guard (match decodeB [[0,0],[1,1],[2,1]] with | none => true | some t => nearTopB t) == false

end Evidence.Region
