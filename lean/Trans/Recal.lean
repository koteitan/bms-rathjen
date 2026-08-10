import Trans.Dict
import Trans.Pair
/-
Trans/Recal.lean — the recalibrated reading oR : BMS.Matrix → Option 𝔗(M) (candidate tier)

After the calibration accident of v0.1.41 the design rule is: do not invent a reading and
then check it against itself.  `oR` is therefore not designed at all — it is

    oR := dict ∘ Trans

where `Trans` is p-adic-lover-bot's translation from the PSS termination proof (ported
below from naruyoko's `common.js` implementation, function by function) and `dict` is the
Buchholz → 𝔗(M) dictionary of Trans/Dict.lean.  Every value can therefore be checked
wholesale against the oracle CLI, and the checks below do exactly that: the Buchholz side
of every `#guard` in §5 is verbatim `pss2bp --raw` output for the matrix in the comment.

Domain: the 2-row fragment (every column of height ≤ 2, matrix nonempty); `none` outside.
Note this is strictly larger than the old `Trans.o?`, whose Stage B additionally required
row-1 entries ≤ 1.  Values are meaningful on standard matrices; `Trans` is total on the
fragment but its output is only claimed to mean anything where the oracle applies.

## What is ported (common.js → this file)

  getPair/lessThanPair   → gp0, gp1                findParent/isParent/isAncestor
  findAncestors          → fAnc                    Pred/Derp/IncrFirst → predP/derp/incrFirst
  isZeroPair/isPrincipalPair/PPair                 isUnadmitted/isAdmitted/Adm
  TrMax/Br/IdxSum/FirstNodes/Joints/jjSeq          Red/isReduced
  PBuchholz/plusBuchholz                → BT.toL/bplus (BT lives in Trans/Dict.lean)
  replaceSCBDecompositionMark           → replMark  (walks the rightmost spine)
  isMarkedBuchholz/nextMarkedBuchholz   → isMarkedB/nextMarkedB
  TransType/Trans/Mark                  → runAux    (one function; `req = none` is Trans,
                                                     `req = some m` is Mark m — the two
                                                     share their whole case structure)

Deviations from the JS, all deliberate:
  * indices are `Int` so that the -1 sentinel of findParent and the negative shifts of
    IncrFirst transcribe literally (Nat truncation would silently differ);
  * every loop is `fuel`-bounded (the JS loops are `while`s whose termination is part of
    p-bot's proof, which is not ported).  Fuel exhaustion cannot pass silently: it changes
    the value, and §5 pins every value against the oracle;
  * `Trans`/`Mark`'s memo tables (TransMemos in the JS) become a `StateM` association
    list.  Without it the recursion re-expands ~3^(columns) times.
  * `SCBDecomposition` and friends are string surgery in the JS and are only used by
    `TransRev`, which is not needed here; the two mark operations that `Trans`/`Mark` do
    use are structural and are ported as such.

Note: the imports precede this comment because the kimina server extracts the header
imports from the top of a posted snippet.
-/

namespace Trans
namespace Recal

open TM (Term)
open Trans.Dict (BT)

/-! ## 1. Pair sequences (the PSS side of common.js) -/

/-- A pair sequence: the 2-row fragment of BMS as (row 0, row 1) columns, indices `Int`
    so that the -1 sentinel and negative `IncrFirst` shifts transcribe literally. -/
abbrev PS := List (Int × Int)

def zeroPS : PS := [(0, 0)]

/-- getPair(M,0,j); out of range reads as 0 (as in the guarded JS accesses). -/
def gp0 (M : PS) (j : Int) : Int := if j < 0 then 0 else (M.getD j.toNat (0, 0)).1
/-- getPair(M,1,j). -/
def gp1 (M : PS) (j : Int) : Int := if j < 0 then 0 else (M.getD j.toNat (0, 0)).2
/-- M.length as an `Int`. -/
def lenI (M : PS) : Int := (M.length : Int)

/-- findParent(M,0,j,k): the greatest j0 with k ≤ j0 < j and M[j0].0 < M[j].0. -/
def fpar0Aux : Nat → PS → Int → Int → Int → Int
  | 0, _, _, _, _ => -1
  | f + 1, M, tgt, j0, k =>
    if j0 < k then -1
    else if gp0 M j0 < tgt then j0
    else fpar0Aux f M tgt (j0 - 1) k

def fpar0 (M : PS) (j k : Int) : Int :=
  if j < 0 ∨ j ≥ lenI M then -1 else fpar0Aux (M.length + 1) M (gp0 M j) (j - 1) k

/-- findParent(M,1,j,k): walk the row-0 parent chain until the row-1 entry drops. -/
def fpar1Aux : Nat → PS → Int → Int → Int → Int
  | 0, _, _, _, _ => -1
  | f + 1, M, tgt, j0, k =>
    let j1 := fpar0 M j0 k
    if j1 < k then -1
    else if gp1 M j1 < tgt then j1
    else fpar1Aux f M tgt j1 k

/-- findParent(M,i,j,k). -/
def fpar (M : PS) (i : Nat) (j k : Int) : Int :=
  if j < 0 ∨ j ≥ lenI M then -1
  else if i == 0 then fpar0Aux (M.length + 1) M (gp0 M j) (j - 1) k
  else fpar1Aux (M.length + 1) M (gp1 M j) j k

/-- isParent(M,i,j,k). -/
def isParentP (M : PS) (i : Nat) (j k : Int) : Bool :=
  decide (0 ≤ k) && decide (k < lenI M) && (k == fpar M i j k)

/-- isAncestor(M,i,j,k). -/
def isAncAux : Nat → PS → Nat → Int → Int → Bool
  | 0, _, _, _, _ => false
  | f + 1, M, i, j0, k =>
    if k == j0 then true
    else
      let j1 := fpar M i j0 k
      if j1 == -1 then false else isAncAux f M i j1 k

def isAnc (M : PS) (i : Nat) (j k : Int) : Bool :=
  if k < 0 ∨ k ≥ lenI M then false else isAncAux (M.length + 1) M i j k

/-- findAncestors(M,i,j,k) (the JS walks with the default k = 0 inside the loop). -/
def fAncAux : Nat → PS → Nat → Int → Int → List Int → List Int
  | 0, _, _, _, _, acc => acc
  | f + 1, M, i, j0, k, acc =>
    let j1 := fpar M i j0 0
    if j1 ≥ k then fAncAux f M i j1 k (acc ++ [j1]) else acc

def fAnc (M : PS) (i : Nat) (j k : Int) : List Int :=
  if j < k ∨ j ≥ lenI M then [] else fAncAux (M.length + 1) M i j k [j]

/-- M.slice(a,b). -/
def slice (M : PS) (a b : Int) : PS := (M.drop a.toNat).take (b - a).toNat
/-- Pred(M). -/
def predP (M : PS) : PS := if M.length == 1 then M else M.dropLast
/-- Derp(M). -/
def derp (M : PS) : PS := M.drop 1
/-- IncrFirst(M,i) (i may be negative). -/
def incrFirst (M : PS) (i : Int) : PS := M.map (fun c => (c.1 + i, c.2))
/-- jjSeq(j0,j1) = (j0,j0)(j0+1,j0+1)…(j1,j1). -/
def jjSeq (j0 j1 : Int) : PS :=
  (List.range (j1 - j0 + 1).toNat).map (fun (k : Nat) => (j0 + Int.ofNat k, j0 + Int.ofNat k))

def isZeroP (M : PS) : Bool := (M.length == 1) && (gp1 M 0 == 0)
def isPrincipalP (M : PS) : Bool := !isZeroP M && isAnc M 0 (lenI M - 1) 0

/-- PPair(M): the decomposition into principal blocks. -/
def ppairAux : Nat → PS → Int → List PS → List PS
  | 0, _, _, acc => acc
  | f + 1, M, j1, acc =>
    if j1 < 0 then acc
    else
      let ans := fAnc M 0 j1 0
      let j0 := (ans.getLast?).getD 0
      ppairAux f M (j0 - 1) (slice M j0 (j1 + 1) :: acc)

def ppair (M : PS) : List PS := ppairAux (M.length + 1) M (lenI M - 1) []

def isUnadmitted (M : PS) (j : Int) : Bool :=
  decide (j > lenI M) || (isParentP M 1 j (j - 1) && isParentP M 1 (j + 1) j)
def isAdm (M : PS) (j : Int) : Bool := !isUnadmitted M j

/-- Adm(M,j): the greatest admitted j0 ≤ j. -/
def admAux : Nat → PS → Int → Int
  | 0, _, _ => 0
  | f + 1, M, j => if j < 0 then 0 else if isAdm M j then j else admAux f M (j - 1)
def adm (M : PS) (j : Int) : Int := admAux (M.length + 2) M j

/-- TrMax(M). -/
def trMaxAux : Nat → PS → Int → Int
  | 0, M, _ => lenI M - 1
  | f + 1, M, j =>
    if j ≥ lenI M then lenI M - 1
    else if !(isParentP M 1 (j + 1) j) then j
    else trMaxAux f M (j + 1)
def trMax (M : PS) : Int := trMaxAux (M.length + 1) M 0

/-- Br(M). -/
def brF (M : PS) : List PS := ppair (M.drop (trMax M + 1).toNat)
/-- IdxSum(Q). -/
def idxSum (Q : List PS) : List Int :=
  (Q.foldl (fun (a : List Int × Int) q => (a.1 ++ [a.2 + (q.length : Int)], a.2 + (q.length : Int)))
    ([0], 0)).1
/-- FirstNodes(M). -/
def firstNodes (M : PS) : List Int := (idxSum (brF M)).map (fun e => trMax M + 1 + e)
/-- Joints(M). -/
def joints (M : PS) : List Int := (firstNodes M).dropLast.map (fun e => fpar M 0 e 0)

/-- Red(M): the reduction to the reduced representative. -/
def red : Nat → PS → PS
  | 0, M => M
  | f + 1, M =>
    if isZeroP M then zeroPS
    else if isPrincipalP M then
      let j1 : Int := lenI M - 1
      if gp0 M 0 == 0 && gp1 M 0 == 0 then
        let j1p := trMax M
        if j1p == j1 then jjSeq 0 j1
        else
          let br := brF M
          let fn := firstNodes M
          let jn := joints M
          (List.range br.length).foldl (init := jjSeq 0 j1p) fun r J =>
            let bJ := br.getD J []
            let nJ : Int := if gp1 bJ 0 == 0 then -1 else fpar M 1 (fn.getD J 0) 0
            let jnJ := jn.getD J 0
            let NJ : PS := (jnJ + 1, nJ + 1) :: derp bJ
            r ++ incrFirst (red f NJ) (jnJ - nJ)
      else
        let m10 := gp1 M 0
        if m10 == 0 then red f (incrFirst M (-(gp0 M 0)))
        else
          let N := red f (jjSeq 0 (m10 - 1) ++ incrFirst M m10)
          let jN : Int := lenI N - 1
          if decide (m10 ≤ jN) && isPrincipalP (N.drop m10.toNat) then
            incrFirst (N.drop m10.toNat) (-(gp0 N m10) + gp1 N m10)
          else M
    else (ppair M).flatMap (red f)

def maxE (M : PS) : Nat :=
  M.foldl (fun a c => Nat.max a (Nat.max c.1.toNat c.2.toNat)) 0
/-- Recursion bound for `red` (see the header note on fuel). -/
def redFuel (M : PS) : Nat := 40 + 4 * (M.length + maxE M)
def redP (M : PS) : PS := red (redFuel M) M
def isReducedP (M : PS) : Bool := redP M == M

/-! ## 2. The Buchholz side (terms live in Trans/Dict.lean) -/

/-- 1 = D_0 0. -/
def bOne : BT := .D 0 .zero
/-- plusBuchholz. -/
def bplus (a b : BT) : BT := BT.ofL (a.toL ++ b.toL)

/-- nextMarkedBuchholz: one step down the rightmost spine. -/
def nextMarkedB : BT → Option BT
  | .zero => none
  | .D _ a => some a
  | t@(.sum _ _) => t.toL.getLast?

/-- isMarkedBuchholz(t,c): does `c` occur on the rightmost spine of `t`? -/
def isMarkedBAux : Nat → Option BT → BT → Bool
  | 0, _, _ => false
  | _ + 1, none, _ => false
  | f + 1, some t, c => if t == c then true else isMarkedBAux f (nextMarkedB t) c
def isMarkedB (t c : BT) : Bool := isMarkedBAux (Dict.BT.size t + 2) (some t) c

/-- replaceSCBDecompositionMark(t,c,cc): replace the occurrence of `c` on the rightmost
    spine of `t` by `cc` (`none` if `c` does not occur there). -/
def replMark : Nat → BT → BT → BT → Option BT
  | 0, _, _, _ => none
  | f + 1, t, c, cc =>
    match t with
    | .zero => none
    | .D u a => if t == c then some cc else (replMark f a c cc).map (fun aa => .D u aa)
    | .sum _ _ =>
      let l := t.toL
      match l.getLast? with
      | none => none
      | some last => (replMark f last c cc).map (fun ll => BT.ofL (l.dropLast ++ [ll]))

/-! ## 3. Trans / Mark  (TransType is inlined into the control flow) -/

/-- The c2 of Trans_internal / Mark_internal, given c1 and the type. -/
def mkC2 (M : PS) (j0 j1 : Int) (ty : Nat) (c1 : BT) : BT :=
  match c1 with
  | .D v t2 =>
    if ty == 1 || ty == 3 || ty == 5 then
      .D v (bplus t2 (.D (gp1 M j1).toNat .zero))
    else if ty == 2 || ty == 4 then
      if t2 == BT.zero then
        .D v (.D (gp1 M j0).toNat (.D (gp1 M j1).toNat .zero))
      else
        let pt2 := t2.toL
        let lastc := (pt2.getLast?).getD BT.zero
        let t34 : BT × BT :=
          match lastc with
          | .D s inner => if (s : Int) == gp1 M j0 then (BT.ofL pt2.dropLast, inner) else (t2, t2)
          | _ => (t2, t2)
        .D v (bplus t34.1 (.D (gp1 M j0).toNat (bplus t34.2 (.D (gp1 M j1).toNat .zero))))
    else
      .D v (.D (gp1 M j1).toNat .zero)
  | _ => BT.zero          -- the JS throws here ("Unexpected error")

/-- The type of TransType_internal, given that M is reduced, principal, j1 ≠ 0 and
    Trans(Pred M) ≠ 0. -/
def transTypeMain (M : PS) (j0 j1 : Int) : Nat :=
  if gp1 M j1 == 0 then (if isAdm M j0 then 1 else 2)
  else if gp1 M j0 ≥ gp1 M j1 then (if isAdm M j0 then 3 else 4)
  else if j0 + 1 < j1 then 5 else 6

/-- Memo table (the JS TransMemos); `none` requests Trans, `some m` requests Mark m. -/
abbrev Memo := List ((PS × Option Int) × BT)
abbrev MM := StateM Memo

/-- Trans (req = none) and Mark m (req = some m) of common.js, memoised. -/
def runAux : Nat → PS → Option Int → MM BT
  | 0, _, _ => pure BT.zero
  | f + 1, M, req => do
    let key : PS × Option Int := (M, req)
    let tbl ← get
    match tbl.find? (fun p => p.1 == key) with
    | some p => pure p.2
    | none => do
      let j1 : Int := lenI M - 1
      let r : BT ←
        if !(isReducedP M) then
          runAux f (redP M) req                                     -- type -3
        else if j1 == 0 then                                        -- type -1
          pure (if gp0 M 0 == 0 && gp1 M 0 == 0 then BT.zero
                else BT.D (gp1 M 0).toNat BT.zero)
        else if !(isPrincipalP M) then                              -- type -2
          match req with
          | none => do
            let ps := ppair M
            let rs ← ps.mapM (fun e => runAux f e none)
            pure (((ps.zip rs).zipIdx).foldl (init := BT.zero) fun a q =>
              if q.2 == 0 then q.1.2
              else bplus a (if q.1.1 == zeroPS then bOne else q.1.2))
          | some m => do
            let pm := ppair M
            let lastq := (pm.getLast?).getD []
            let j0 : Int := j1 - (lastq.length : Int) + 1
            if lastq == zeroPS then pure bOne else runAux f lastq (some (m - j0))
        else do
          let t1 ← runAux f (predP M) none
          if t1 == BT.zero then                                     -- type 0
            match req with
            | none => pure (BT.D 0 (BT.D (gp1 M j1).toNat BT.zero))
            | some m =>
              pure (if m == 0 then BT.D 0 (BT.D (gp1 M j1).toNat BT.zero)
                    else BT.D (gp1 M j1).toNat BT.zero)
          else do                                                   -- types 1–6
            let j0 := fpar M 0 j1 0
            let ty := transTypeMain M j0 j1
            let jn1 := adm M j0
            let c1 ← runAux f (predP M) (some jn1)
            let c2 := mkC2 M j0 j1 ty c1
            let dep := Dict.BT.size c1 + Dict.BT.size c2 + 4
            match req with
            | none => pure ((replMark (Dict.BT.size t1 + dep) t1 c1 c2).getD BT.zero)
            | some m =>
              if m < j1 then do
                let c0 ← runAux f (predP M) (some m)
                pure (if isMarkedB c0 c1 then
                        (replMark (Dict.BT.size c0 + dep) c0 c1 c2).getD BT.zero
                      else BT.D (gp1 M j1).toNat BT.zero)
              else pure (BT.D (gp1 M j1).toNat BT.zero)
      modify (fun tbl => (key, r) :: tbl)
      pure r

/-- Recursion bound for Trans/Mark (see the header note on fuel). -/
def transFuel (M : PS) : Nat := 40 + 6 * (M.length + maxE M)

/-- Trans(M) of common.js. -/
def transPort (M : PS) : BT := (runAux (transFuel M) M none).run' []

/-! ## 4. oR -/

/-- The 2-row fragment: nonempty, every column of height ≤ 2. -/
def ofMatrix (m : BMS.Matrix) : Option PS :=
  if !m.isEmpty && m.all (fun c => decide (c.length ≤ 2)) then
    some (m.map (fun c => ((c.getD 0 0 : Int), (c.getD 1 0 : Int))))
  else none

/-- The recalibrated reading, Buchholz side (the oracle's own target). -/
def oRB (m : BMS.Matrix) : Option BT := (ofMatrix m).map transPort

/-- The recalibrated reading: oR = (1 + ·) ∘ dict ∘ Trans.

    The `1 +` is a *convention* adjustment, not a fudge: this repository treats the empty
    matrix as 0 (`Trans.o? [] = 0`, `Trans.o? (0,0) = 1`), while a PSS pair sequence is
    never empty and p-bot's Trans starts the count at Trans((0,0)) = 0.  The two readings
    therefore differ by exactly one everywhere and by nothing at all above ω, since
    1 + α = α for α ≥ ω.  Dropping the adjustment would move every row of the table's
    finite region down by one; keeping it makes `oR` agree with the old `Trans.o?`
    verbatim on the whole region where `o?` was oracle-confirmed (checked below). -/
def oR (m : BMS.Matrix) : Option Term :=
  if m.isEmpty then some TM.Term.zero
  else (oRB m).map (fun t => TM.Term.plus TM.Term.one (Dict.dict t))

/-! ## 5. Acceptance record

  (A) the mandatory negative controls — the v0.1.41 memorial;
  (B) the oracle table: `oRB` against verbatim `pss2bp --raw` output, wholesale;
  (C) `oR` = the old `Trans.o?` on the whole region where `o?` was confirmed, and
      `oR` ≠ `o?` on every corpus matrix at or above the withdrawal boundary;
  (D) every produced term satisfies `inT` ([R91] 2.1).

The `#guard`s below are the frozen part.  During development the same checks ran over
3161 standard matrices (up to 24 columns) generated by closing 15 seeds under `fundPair`
and prefixes: zero mismatches against the oracle. -/

namespace Test

open BMS (Matrix)
open Evidence (corpus)
open TM.Term

/-- stringifyBuchholz(t,false) of common.js — so that the expected values below can be
    compared by eye with `node pss2bp.js --raw "(0,0)(1,1)…"`. -/
def showRawF : Nat → BT → String
  | 0, _ => "?"
  | f + 1, t =>
    match t with
    | .zero => "0"
    | .D u a => "D_" ++ toString u ++ " " ++ showRawF f a
    | .sum _ _ => "(" ++ String.intercalate "," (t.toL.map (showRawF f)) ++ ")"
def showRaw (t : BT) : String := showRawF (Dict.BT.size t + 2) t
def rawOf (m : Matrix) : String := ((oRB m).map showRaw).getD "NONE"

/-! ### (A) the mandatory negative controls

Each is a value the miscalibrated `o?` produced and the oracle refutes.  They are
non-vacuous: `oR` is defined on all three matrices (first three guards), and the value it
does produce is pinned (last three).  Re-introducing any of the three refuted readings
turns this file red. -/

#guard (oR [[0,0],[1,1],[2,1],[2,1]]).isSome
#guard (oR [[0,0],[1,1],[2,1],[2,0]]).isSome
#guard (oR [[0,0],[1,1],[2,2]]).isSome

-- the ζ₁ mistake: (0,0)(1,1)(2,1)(2,1) is NOT ζ₁ (o? said φ̄(2,1); oracle: D_0 D_1(Ω_1×2))
#guard oR [[0,0],[1,1],[2,1],[2,1]] != some (phi (ofNat 2) one)
-- the ε_{ζ₀·ω} mistake: (0,0)(1,1)(2,1)(2,0) (o? said φ̄(1,ω̄^{ζ₀+1}); oracle: D_0 D_1(Ω_1+1))
#guard oR [[0,0],[1,1],[2,1],[2,0]] != some (phi one (phi zero (phi (ofNat 2) zero)))
-- the φ̄(ω,0) mistake: (0,0)(1,1)(2,2) (o? said φ̄(ω,0); oracle: D_0 Ω_2)
#guard oR [[0,0],[1,1],[2,2]] != some (phi omega zero)

-- what they are instead
#guard oR [[0,0],[1,1],[2,1],[2,1]] == some (phi (ofNat 3) zero)          -- φ̄(3,0)
#guard oR [[0,0],[1,1],[2,1],[2,0]] == some (phi (ofNat 2) omega)         -- ζ_ω
#guard oR [[0,0],[1,1],[2,2]] == some (psi (Z zero) (Z one))              -- ψ_{Z0}(Ω₂)
-- and the row that used to carry φ̄(3,0) is Γ₀
#guard oR [[0,0],[1,1],[2,1],[3,1]] == some (psi (Z zero) zero)           -- Γ₀
-- while φ̄(ω,0) is the value of (0,0)(1,1)(2,1)(3,0)
#guard oR [[0,0],[1,1],[2,1],[3,0]] == some (phi omega zero)

/-! ### (B) the oracle table

Every row of `table/oracle-audit-2026-08-09.txt`.  The right-hand side is verbatim
`node pss2bp.js --raw "<matrix>"` output, so a reader can re-derive it from the CLI. -/

private def auditRows : List (Matrix × String) := [
  ([[0,0], [1,1]],
   "D_0 D_1 0"),   -- (0,0)(1,1)
  ([[0,0], [1,1], [0,0]],
   "(D_0 D_1 0,D_0 0)"),   -- (0,0)(1,1)(0,0)
  ([[0,0], [1,1], [1,0]],
   "D_0 (D_1 0,D_0 0)"),   -- (0,0)(1,1)(1,0)
  ([[0,0], [1,1], [1,1]],
   "D_0 (D_1 0,D_1 0)"),   -- (0,0)(1,1)(1,1)
  ([[0,0], [1,1], [2,0]],
   "D_0 D_1 D_0 0"),   -- (0,0)(1,1)(2,0)
  ([[0,0], [1,1], [2,0], [0,0]],
   "(D_0 D_1 D_0 0,D_0 0)"),   -- (0,0)(1,1)(2,0)(0,0)
  ([[0,0], [1,1], [2,0], [2,0]],
   "D_0 D_1 (D_0 0,D_0 0)"),   -- (0,0)(1,1)(2,0)(2,0)
  ([[0,0], [1,1], [2,0], [3,0]],
   "D_0 D_1 D_0 D_0 0"),   -- (0,0)(1,1)(2,0)(3,0)
  ([[0,0], [1,1], [2,0], [3,1]],
   "D_0 D_1 D_0 D_1 0"),   -- (0,0)(1,1)(2,0)(3,1)
  ([[0,0], [1,1], [2,1]],
   "D_0 D_1 D_1 0"),   -- (0,0)(1,1)(2,1)
  ([[0,0], [1,1], [2,1], [0,0]],
   "(D_0 D_1 D_1 0,D_0 0)"),   -- (0,0)(1,1)(2,1)(0,0)
  ([[0,0], [1,1], [2,1], [1,0]],
   "D_0 (D_1 D_1 0,D_0 0)"),   -- (0,0)(1,1)(2,1)(1,0)
  ([[0,0], [1,1], [2,1], [1,1]],
   "D_0 (D_1 D_1 0,D_1 0)"),   -- (0,0)(1,1)(2,1)(1,1)
  ([[0,0], [1,1], [2,1], [2,0]],
   "D_0 D_1 (D_1 0,D_0 0)"),   -- (0,0)(1,1)(2,1)(2,0)
  ([[0,0], [1,1], [2,1], [2,1]],
   "D_0 D_1 (D_1 0,D_1 0)"),   -- (0,0)(1,1)(2,1)(2,1)
  ([[0,0], [1,1], [2,1], [3,0]],
   "D_0 D_1 D_1 D_0 0"),   -- (0,0)(1,1)(2,1)(3,0)
  ([[0,0], [1,1], [2,1], [3,0], [4,1]],
   "D_0 D_1 D_1 D_0 D_1 0"),   -- (0,0)(1,1)(2,1)(3,0)(4,1)
  ([[0,0], [1,1], [2,1], [3,1]],
   "D_0 D_1 D_1 D_1 0"),   -- (0,0)(1,1)(2,1)(3,1)
  ([[0,0], [1,1], [2,1], [3,1], [0,0]],
   "(D_0 D_1 D_1 D_1 0,D_0 0)"),   -- (0,0)(1,1)(2,1)(3,1)(0,0)
  ([[0,0], [1,1], [2,1], [3,1], [1,0]],
   "D_0 (D_1 D_1 D_1 0,D_0 0)"),   -- (0,0)(1,1)(2,1)(3,1)(1,0)
  ([[0,0], [1,1], [2,2]],
   "D_0 D_2 0"),   -- (0,0)(1,1)(2,2)
  ([[0,0], [1,1], [2,2], [1,1]],
   "D_0 (D_2 0,D_1 0)"),   -- (0,0)(1,1)(2,2)(1,1)
  ([[0,0], [1,1], [2,2], [1,1], [2,1]],
   "D_0 (D_2 0,D_1 D_1 0)"),   -- (0,0)(1,1)(2,2)(1,1)(2,1)
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,1]],
   "D_0 (D_2 0,D_1 D_1 D_1 0)"),   -- (0,0)(1,1)(2,2)(1,1)(2,1)(3,1)
  ([[0,0], [1,1], [2,2], [1,1], [2,2]],
   "D_0 (D_2 0,D_1 D_2 0)"),   -- (0,0)(1,1)(2,2)(1,1)(2,2)
  ([[0,0], [1,1], [2,2], [1,1], [2,2], [1,1], [2,2]],
   "D_0 (D_2 0,D_1 D_2 0,D_1 D_2 0)"),   -- (0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)
  ([[0,0], [1,1], [2,2], [2,0]],
   "D_0 (D_2 0,D_1 (D_2 0,D_0 0))"),   -- (0,0)(1,1)(2,2)(2,0)
  ([[0,0], [1,1], [2,2], [2,0], [2,0]],
   "D_0 (D_2 0,D_1 (D_2 0,D_0 0,D_0 0))"),   -- (0,0)(1,1)(2,2)(2,0)(2,0)
  ([[0,0], [1,1], [2,2], [2,0], [3,0]],
   "D_0 (D_2 0,D_1 (D_2 0,D_0 D_0 0))"),   -- (0,0)(1,1)(2,2)(2,0)(3,0)
  ([[0,0], [1,1], [2,2], [2,0], [3,1]],
   "D_0 (D_2 0,D_1 (D_2 0,D_0 D_1 0))"),   -- (0,0)(1,1)(2,2)(2,0)(3,1)
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,2]],
   "D_0 (D_2 0,D_1 (D_2 0,D_0 D_2 0))"),   -- (0,0)(1,1)(2,2)(2,0)(3,1)(4,2)
  ([[0,0], [1,1], [2,2], [2,1]],
   "D_0 (D_2 0,D_1 (D_2 0,D_1 0))"),   -- (0,0)(1,1)(2,2)(2,1)
  ([[0,0], [1,1], [2,2], [2,1], [2,1]],
   "D_0 (D_2 0,D_1 (D_2 0,D_1 0,D_1 0))"),   -- (0,0)(1,1)(2,2)(2,1)(2,1)
  ([[0,0], [1,1], [2,2], [2,1], [3,1]],
   "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 0))"),   -- (0,0)(1,1)(2,2)(2,1)(3,1)
  ([[0,0], [1,1], [2,2], [2,1], [3,2]],
   "D_0 (D_2 0,D_1 (D_2 0,D_1 D_2 0))"),   -- (0,0)(1,1)(2,2)(2,1)(3,2)
  ([[0,0], [1,1], [2,2], [2,2]],
   "D_0 (D_2 0,D_2 0)"),   -- (0,0)(1,1)(2,2)(2,2)
  ([[0,0], [1,1], [2,2], [2,2], [2,2]],
   "D_0 (D_2 0,D_2 0,D_2 0)"),   -- (0,0)(1,1)(2,2)(2,2)(2,2)
  ([[0,0], [1,1], [2,2], [3,0]],
   "D_0 D_2 D_0 0"),   -- (0,0)(1,1)(2,2)(3,0)
  ([[0,0], [1,1], [2,2], [3,0], [3,0]],
   "D_0 D_2 (D_0 0,D_0 0)"),   -- (0,0)(1,1)(2,2)(3,0)(3,0)
  ([[0,0], [1,1], [2,2], [3,0], [4,0]],
   "D_0 D_2 D_0 D_0 0"),   -- (0,0)(1,1)(2,2)(3,0)(4,0)
  ([[0,0], [1,1], [2,2], [3,0], [4,1]],
   "D_0 D_2 D_0 D_1 0"),   -- (0,0)(1,1)(2,2)(3,0)(4,1)
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2]],
   "D_0 D_2 D_0 D_2 0"),   -- (0,0)(1,1)(2,2)(3,0)(4,1)(5,2)
  ([[0,0], [1,1], [2,2], [3,1]],
   "D_0 D_2 D_1 0"),   -- (0,0)(1,1)(2,2)(3,1)
]

#guard auditRows.all fun p => (oRB p.1).isSome
#guard auditRows.all fun p => rawOf p.1 == p.2

/-- A systematic corpus: 15 seeds closed under `fundPair` and prefixes, restricted to
    standard pair sequences (`isStandardPair` of common.js); values from the same CLI. -/
private def corpusRows : List (Matrix × String) := [
  ([[0,0]], "0"),
  ([[0,0], [0,0]], "D_0 0"),
  ([[0,0], [1,0]], "D_0 D_0 0"),
  ([[0,0], [1,1]], "D_0 D_1 0"),
  ([[0,0], [0,0], [0,0]], "(D_0 0,D_0 0)"),
  ([[0,0], [1,0], [1,0]], "D_0 (D_0 0,D_0 0)"),
  ([[0,0], [1,0], [2,0]], "D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,0]], "D_0 D_1 D_0 0"),
  ([[0,0], [1,1], [2,1]], "D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2]], "D_0 D_2 0"),
  ([[0,0], [1,0], [1,0], [1,0]], "D_0 (D_0 0,D_0 0,D_0 0)"),
  ([[0,0], [1,1], [2,0], [3,0]], "D_0 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,0], [3,1]], "D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,1], [2,0]], "D_0 D_1 (D_1 0,D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,1]], "D_0 D_1 (D_1 0,D_1 0)"),
  ([[0,0], [1,1], [2,1], [3,0]], "D_0 D_1 D_1 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,1]], "D_0 D_1 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,0]], "D_0 (D_2 0,D_0 0)"),
  ([[0,0], [1,1], [2,2], [1,1]], "D_0 (D_2 0,D_1 0)"),
  ([[0,0], [1,1], [2,2], [2,0]], "D_0 (D_2 0,D_1 (D_2 0,D_0 0))"),
  ([[0,0], [1,1], [2,2], [2,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,2]], "D_0 (D_2 0,D_2 0)"),
  ([[0,0], [1,1], [2,2], [3,0]], "D_0 D_2 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,1]], "D_0 D_2 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,2]], "D_0 D_2 D_2 0"),
  ([[0,0], [1,1], [2,2], [3,3]], "D_0 D_3 0"),
  ([[0,0], [1,1], [2,0], [3,0], [4,0]], "D_0 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,0], [3,1], [4,0]], "D_0 D_1 D_0 D_1 D_0 0"),
  ([[0,0], [1,1], [2,1], [1,1], [2,1]], "D_0 (D_1 D_1 0,D_1 D_1 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,0]], "D_0 D_1 (D_1 0,D_0 D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1]], "D_0 D_1 (D_1 0,D_0 D_1 0)"),
  ([[0,0], [1,1], [2,1], [2,1], [2,1]], "D_0 D_1 (D_1 0,D_1 0,D_1 0)"),
  ([[0,0], [1,1], [2,1], [3,0], [4,0]], "D_0 D_1 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1]], "D_0 D_1 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1]], "D_0 (D_2 0,D_0 D_1 0)"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0]], "D_0 (D_2 0,D_1 D_0 0)"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1]], "D_0 (D_2 0,D_1 D_1 0)"),
  ([[0,0], [1,1], [2,2], [1,1], [2,2]], "D_0 (D_2 0,D_1 D_2 0)"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1]], "D_0 (D_2 0,D_1 (D_2 0,D_0 D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_2 0))"),
  ([[0,0], [1,1], [2,2], [2,2], [2,2]], "D_0 (D_2 0,D_2 0,D_2 0)"),
  ([[0,0], [1,1], [2,2], [3,0], [3,0]], "D_0 D_2 (D_0 0,D_0 0)"),
  ([[0,0], [1,1], [2,2], [3,0], [4,0]], "D_0 D_2 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1]], "D_0 D_2 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,1]], "D_0 D_2 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2]], "D_0 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1]], "D_0 D_2 D_2 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,2]], "D_0 D_2 D_2 D_2 0"),
  ([[0,0], [1,1], [2,0], [3,1], [4,0], [5,0]], "D_0 D_1 D_0 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,0], [3,1], [4,0], [5,1]], "D_0 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,1], [2,0], [3,0], [4,0]], "D_0 D_1 (D_1 0,D_0 D_0 D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,0]], "D_0 D_1 (D_1 0,D_0 D_1 D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1]], "D_0 D_1 (D_1 0,D_0 D_1 D_1 0)"),
  ([[0,0], [1,1], [2,1], [3,0], [4,0], [5,0]], "D_0 D_1 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,0]], "D_0 D_1 D_1 D_0 D_1 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1]], "D_0 D_1 D_1 D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1], [3,1]], "D_0 (D_2 0,D_0 D_1 D_1 0)"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1], [3,2]], "D_0 (D_2 0,D_0 D_2 0)"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1]], "D_0 (D_2 0,D_1 D_0 D_1 0)"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0]], "D_0 (D_2 0,D_1 D_1 D_0 0)"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,1]], "D_0 (D_2 0,D_1 D_1 D_1 0)"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,1]], "D_0 (D_2 0,D_1 (D_2 0,D_0 D_1 D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,2]], "D_0 (D_2 0,D_1 (D_2 0,D_0 D_2 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_1 0))"),
  ([[0,0], [1,1], [2,2], [3,0], [3,0], [3,0]], "D_0 D_2 (D_0 0,D_0 0,D_0 0)"),
  ([[0,0], [1,1], [2,2], [3,0], [4,0], [4,0]], "D_0 D_2 D_0 (D_0 0,D_0 0)"),
  ([[0,0], [1,1], [2,2], [3,0], [4,0], [5,0]], "D_0 D_2 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,0]], "D_0 D_2 D_0 D_1 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1]], "D_0 D_2 D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2]], "D_0 D_2 D_0 D_2 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,1], [5,1]], "D_0 D_2 D_1 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,1]], "D_0 D_2 D_1 D_2 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2]], "D_0 D_2 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,0], [3,1], [4,0], [5,0], [6,0]], "D_0 D_1 D_0 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [1,1], [2,1], [1,1], [2,1]], "D_0 (D_1 D_1 0,D_1 D_1 0,D_1 D_1 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,0], [5,0]], "D_0 D_1 (D_1 0,D_0 D_1 D_0 D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,0], [5,1]], "D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 0))"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,0], [6,0]], "D_0 D_1 D_1 D_0 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,0], [6,1]], "D_0 D_1 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [5,1]], "D_0 D_1 D_1 D_0 D_1 (D_1 0,D_1 0)"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 0"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1], [3,1], [4,1]], "D_0 (D_2 0,D_0 D_1 D_1 D_1 0)"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1], [3,2], [2,0]], "D_0 (D_2 0,D_0 (D_2 0,D_0 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2]], "D_0 (D_2 0,D_1 D_0 D_2 0)"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1]], "D_0 (D_2 0,D_1 D_1 D_0 D_1 0)"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,1], [5,1]], "D_0 (D_2 0,D_1 (D_2 0,D_0 D_1 D_1 D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,2], [4,0]], "D_0 (D_2 0,D_1 (D_2 0,D_0 (D_2 0,D_1 (D_2 0,D_0 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 D_2 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,2], [3,1], [4,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 (D_2 0,D_1 D_2 0)))"),
  ([[0,0], [1,1], [2,2], [2,2], [2,1], [3,2], [3,2]], "D_0 (D_2 0,D_2 0,D_1 (D_2 0,D_2 0,D_1 (D_2 0,D_2 0)))"),
  ([[0,0], [1,1], [2,2], [3,0], [4,0], [4,0], [4,0]], "D_0 D_2 D_0 (D_0 0,D_0 0,D_0 0)"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,0], [6,0]], "D_0 D_2 D_0 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,0], [6,1]], "D_0 D_2 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0]], "D_0 D_2 D_0 D_1 D_1 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,1]], "D_0 D_2 D_0 D_1 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [5,2]], "D_0 D_2 D_0 (D_2 0,D_2 0)"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0]], "D_0 D_2 D_0 D_2 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,1], [6,1]], "D_0 D_2 D_1 D_2 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,1], [6,2]], "D_0 D_2 D_1 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2], [6,2]], "D_0 D_2 D_2 D_1 D_2 D_2 0"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,0], [5,0], [6,0]], "D_0 D_1 (D_1 0,D_0 D_1 D_0 D_0 D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,0], [5,1], [6,0]], "D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [3,1], [4,1]], "D_0 D_1 (D_1 0,D_0 (D_1 D_1 0,D_1 D_1 0))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_0 0))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 0))"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,0], [6,0], [7,0]], "D_0 D_1 D_1 D_0 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,0], [6,1], [7,0]], "D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [5,1], [5,1]], "D_0 D_1 D_1 D_0 D_1 (D_1 0,D_1 0,D_1 0)"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1], [3,2], [2,0], [3,1]], "D_0 (D_2 0,D_0 (D_2 0,D_0 D_1 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,1]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2]], "D_0 (D_2 0,D_1 D_1 D_0 D_2 0)"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,2], [4,0], [5,1]], "D_0 (D_2 0,D_1 (D_2 0,D_0 (D_2 0,D_1 (D_2 0,D_0 D_1 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 D_2 0))"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,0], [6,0], [7,0]], "D_0 D_2 D_0 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,0], [6,1], [7,0]], "D_0 D_2 D_0 D_1 D_0 D_1 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [5,2], [5,2]], "D_0 D_2 D_0 (D_2 0,D_2 0,D_2 0)"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,0]], "D_0 D_2 D_0 D_2 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,1]], "D_0 D_2 D_0 D_2 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,0], [5,1], [6,2], [7,1]], "D_0 D_2 D_1 D_0 D_2 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,1], [6,1], [7,1]], "D_0 D_2 D_1 D_2 D_1 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2], [6,1], [7,2]], "D_0 D_2 D_2 D_1 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2], [6,2], [7,1]], "D_0 D_2 D_2 D_1 D_2 D_2 D_1 0"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,0], [5,1], [6,0], [7,0]], "D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 D_0 D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,0], [5,1], [6,0], [7,1]], "D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 D_0 D_1 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,0], [6,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_0 D_0 0))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_0 0))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,1]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_1 0))"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,0], [6,1], [7,0], [8,0]], "D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,0], [6,1], [7,0], [8,1]], "D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,0], [8,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,1]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1], [3,2], [2,0], [3,1], [4,1]], "D_0 (D_2 0,D_0 (D_2 0,D_0 D_1 D_1 0))"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1], [3,2], [2,0], [3,1], [4,2]], "D_0 (D_2 0,D_0 (D_2 0,D_0 D_2 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,1], [4,0]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 D_0 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,2], [4,0], [5,1], [6,1]], "D_0 (D_2 0,D_1 (D_2 0,D_0 (D_2 0,D_1 (D_2 0,D_0 D_1 D_1 0))))"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,2], [4,0], [5,1], [6,2]], "D_0 (D_2 0,D_1 (D_2 0,D_0 (D_2 0,D_1 (D_2 0,D_0 D_2 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,1], [6,0]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 0))))"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,0], [6,1], [7,0], [8,0]], "D_0 D_2 D_0 D_1 D_0 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,0], [6,1], [7,0], [8,1]], "D_0 D_2 D_0 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1], [8,1]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,0], [8,0]], "D_0 D_2 D_0 D_2 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,1], [8,1]], "D_0 D_2 D_0 D_2 D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,1], [8,2]], "D_0 D_2 D_0 D_2 D_0 D_2 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2], [6,2], [7,1], [8,2]], "D_0 D_2 D_2 D_1 D_2 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,0], [5,1], [6,0], [7,0], [8,0]], "D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 D_0 D_0 D_0 0)"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [3,1], [4,1], [3,1], [4,1]], "D_0 D_1 (D_1 0,D_0 (D_1 D_1 0,D_1 D_1 0,D_1 D_1 0))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,0], [7,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_0 D_0 0))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,0], [7,1]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 0))"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,0], [6,1], [7,0], [8,0], [9,0]], "D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,1]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,0], [2,1], [3,2], [2,0], [3,1], [4,1], [5,1]], "D_0 (D_2 0,D_0 (D_2 0,D_0 D_1 D_1 D_1 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,0], [4,1], [5,2]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_0 D_2 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,1], [4,0], [5,1]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 D_0 D_1 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,0], [3,1], [4,2], [4,0], [5,1], [6,1], [7,1]], "D_0 (D_2 0,D_1 (D_2 0,D_0 (D_2 0,D_1 (D_2 0,D_0 D_1 D_1 D_1 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,0], [6,1], [7,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_0 D_2 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,1], [6,0], [7,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 D_1 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 0))))"),
  ([[0,0], [1,1], [2,2], [2,2], [2,1], [3,2], [3,2], [3,1], [4,2], [4,2]], "D_0 (D_2 0,D_2 0,D_1 (D_2 0,D_2 0,D_1 (D_2 0,D_2 0,D_1 (D_2 0,D_2 0))))"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,0], [6,1], [7,0], [8,0], [9,0]], "D_0 D_2 D_0 D_1 D_0 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,1]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1], [8,1], [9,0]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_1 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,1], [8,0], [9,1]], "D_0 D_2 D_0 D_2 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,1], [8,1], [9,1]], "D_0 D_2 D_0 D_2 D_0 D_1 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,1], [5,0], [6,1], [7,2], [8,1], [9,1]], "D_0 D_2 D_1 D_1 D_0 D_2 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,0], [6,1], [7,2], [8,1], [9,2]], "D_0 D_2 D_1 D_2 D_0 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2], [6,1], [7,2], [8,1], [9,2]], "D_0 D_2 D_2 D_1 D_2 D_1 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2], [6,2], [7,1], [8,2], [9,2]], "D_0 D_2 D_2 D_1 D_2 D_2 D_1 D_2 D_2 0"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,0], [7,0], [8,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_0 D_0 D_0 0))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,0], [7,1], [8,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 D_0 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,1], [4,0], [5,1], [6,2]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 D_0 D_2 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,1], [6,0]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 D_0 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,1], [6,0], [7,1], [8,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 D_2 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,1], [8,0]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 0))))"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,0], [10,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,1], [10,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1], [8,1], [9,0], [10,1]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2], [6,2], [7,1], [8,2], [9,1], [10,2]], "D_0 D_2 D_2 D_1 D_2 D_2 D_1 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,0], [7,1], [8,0], [9,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 D_0 D_0 0))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,0], [7,1], [8,0], [9,1]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 D_0 D_1 0))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,1], [4,0], [5,1], [6,2], [5,1]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 0)))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,1], [6,0], [7,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 D_0 D_1 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,1], [6,0], [7,1], [8,2], [8,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 0))))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,1], [8,0], [9,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 D_1 0))))"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,1], [10,0], [11,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 D_0 0"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,1], [10,0], [11,1]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,1], [10,0], [11,1]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1], [8,1], [9,0], [10,1], [11,1]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,1], [8,0], [9,1], [10,0], [11,1]], "D_0 D_2 D_0 D_2 D_0 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,1], [8,1], [9,0], [10,1], [11,1]], "D_0 D_2 D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,0], [5,1], [6,2], [7,1], [8,0], [9,1], [10,2], [11,1]], "D_0 D_2 D_1 D_0 D_2 D_1 D_0 D_2 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,1], [6,0], [7,1], [8,2], [9,1], [10,2], [11,1]], "D_0 D_2 D_1 D_2 D_1 D_0 D_2 D_1 D_2 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,0], [4,1], [5,2], [4,0], [5,1], [6,2]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_0 (D_2 0,D_0 D_2 0)))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,0], [6,1], [7,2], [6,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 0)))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,1], [6,0], [7,1], [8,2]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 D_0 D_2 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,0], [6,1], [7,2], [7,0], [8,1], [9,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_0 (D_2 0,D_1 (D_2 0,D_0 D_2 0))))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,0], [8,1], [9,2], [9,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 0))))))"),
  ([[0,0], [1,1], [2,1], [2,0], [3,1], [4,1], [4,0], [5,1], [6,0], [7,1], [8,0], [9,0], [10,0]], "D_0 D_1 (D_1 0,D_0 D_1 (D_1 0,D_0 D_1 D_0 D_1 D_0 D_0 D_0 0))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,1], [8,0], [9,1], [10,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 D_2 0))))"),
  ([[0,0], [1,1], [2,1], [3,0], [4,1], [5,1], [6,0], [7,1], [8,0], [9,1], [10,0], [11,0], [12,0]], "D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 D_0 D_0 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1], [8,1], [9,0], [10,1], [11,0], [12,1]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,2], [4,1], [5,2], [6,2], [7,1], [8,2], [9,1], [10,2], [11,1], [12,2]], "D_0 D_2 D_2 D_1 D_2 D_2 D_1 D_2 D_1 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,1], [4,0], [5,1], [6,2], [5,0], [6,1], [7,2]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_0 D_2 0)))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,1], [6,0], [7,1], [8,2], [7,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 0)))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,1], [6,0], [7,1], [8,2], [8,0], [9,1], [10,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_0 D_2 0))))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,1], [8,0], [9,1], [10,2], [10,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 0))))))"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,1], [6,1], [7,0], [8,1], [9,2], [10,1], [11,2], [12,1], [13,1]], "D_0 D_2 D_1 D_2 D_1 D_1 D_0 D_2 D_1 D_2 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,1], [6,0], [7,1], [8,2], [7,1], [8,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 0)))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,1], [8,0], [9,1], [10,2], [10,1], [11,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 0))))))"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,1], [6,0], [7,1], [8,1], [9,0], [10,1], [11,0], [12,1], [13,0], [14,1]], "D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_0 D_1 D_0 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,0], [4,1], [5,2], [6,0], [7,1], [8,1], [9,0], [10,1], [11,1], [12,0], [13,1], [14,1]], "D_0 D_2 D_0 D_2 D_0 D_1 D_1 D_0 D_1 D_1 D_0 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,1], [5,0], [6,1], [7,2], [8,1], [9,1], [10,0], [11,1], [12,2], [13,1], [14,1]], "D_0 D_2 D_1 D_1 D_0 D_2 D_1 D_1 D_0 D_2 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,0], [6,1], [7,2], [8,1], [9,2], [10,0], [11,1], [12,2], [13,1], [14,2]], "D_0 D_2 D_1 D_2 D_0 D_2 D_1 D_2 D_0 D_2 D_1 D_2 0"),
  ([[0,0], [1,1], [2,2], [1,1], [2,0], [3,1], [4,2], [3,1], [4,0], [5,1], [6,2], [5,0], [6,1], [7,2], [6,0], [7,1], [8,2]], "D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_0 (D_2 0,D_0 D_2 0))))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,0], [6,1], [7,2], [6,1], [7,0], [8,1], [9,2], [8,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,0], [4,1], [5,2], [5,1], [6,0], [7,1], [8,2], [8,0], [9,1], [10,2], [10,0], [11,1], [12,2]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_0 (D_2 0,D_1 (D_2 0,D_0 D_2 0))))))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,0], [8,1], [9,2], [9,1], [10,0], [11,1], [12,2], [12,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 0))))))))"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,1], [6,0], [7,1], [8,2], [7,1], [8,0], [9,1], [10,2], [9,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 0))))"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,1], [8,0], [9,1], [10,2], [10,1], [11,0], [12,1], [13,2], [13,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 0))))))))"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,1], [6,0], [7,1], [8,2], [9,1], [10,2], [11,1], [12,0], [13,1], [14,2], [15,1], [16,2], [17,1]], "D_0 D_2 D_1 D_2 D_1 D_0 D_2 D_1 D_2 D_1 D_0 D_2 D_1 D_2 D_1 0"),
  ([[0,0], [1,1], [2,2], [1,1], [2,1], [3,0], [4,1], [5,2], [4,1], [5,1], [6,0], [7,1], [8,2], [7,1], [8,0], [9,1], [10,2], [9,1], [10,0], [11,1], [12,2], [11,1]], "D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 D_0 (D_2 0,D_1 0)))))"),
  ([[0,0], [1,1], [2,2], [3,1], [4,2], [5,1], [6,1], [7,0], [8,1], [9,2], [10,1], [11,2], [12,1], [13,1], [14,0], [15,1], [16,2], [17,1], [18,2], [19,1], [20,1]], "D_0 D_2 D_1 D_2 D_1 D_1 D_0 D_2 D_1 D_2 D_1 D_1 D_0 D_2 D_1 D_2 D_1 D_1 0"),
  ([[0,0], [1,1], [2,2], [2,1], [3,1], [4,0], [5,1], [6,2], [6,1], [7,1], [8,0], [9,1], [10,2], [10,1], [11,0], [12,1], [13,2], [13,1], [14,0], [15,1], [16,2], [16,1]], "D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 D_0 (D_2 0,D_1 (D_2 0,D_1 0))))))))))")
]

#guard corpusRows.length == 237
#guard corpusRows.all fun p => (oRB p.1).isSome
#guard corpusRows.all fun p => rawOf p.1 == p.2
#guard corpusRows.all fun p => ((oR p.1).map inT).getD false


/-! ### (C) against the old `Trans.o?`

`bnd` is the withdrawal boundary of v0.1.41: `o?` was confirmed against the oracle
strictly below it and is wrong at and above it. -/

def bnd : Matrix := [[0,0],[1,1],[2,1],[2,0]]
def below (m : Matrix) : Bool := BMS.cmpM m bnd == .lt

private def cc : List Matrix :=
  corpus [[0,0],[1,1],[1,1]] 3 3 ++ corpus [[0,0],[1,1],[2,0]] 3 3 ++
  corpus [[0,0],[1,1],[2,1]] 3 3 ++ corpus [[0,0],[1,1],[2,0],[3,1]] 3 3 ++
  corpus [[0],[1],[2]] 4 3 ++ corpus [[0,0],[1,1],[2,1],[3,1]] 3 3 ++
  corpus [[0,0],[1,1],[2,2]] 4 3
private def ccb : List Matrix := cc.filter (fun m => below m && (Trans.o? m).isSome)
private def cca : List Matrix := cc.filter (fun m => !below m && (Trans.o? m).isSome)

-- below the boundary: oR reproduces the old reading exactly (203 matrices)
#guard ccb.all fun m => oR m == Trans.o? m
-- at/above it: oR differs from the old reading on every single one (54 matrices) —
-- this is the recalibration, and it is what the withdrawal of v0.1.42 was about
#guard cca.all fun m => oR m != Trans.o? m
#guard ccb.length == 203 && cca.length == 54

/-! ### (D) wellformedness -/

#guard cc.all fun m => ((oR m).map inT).getD true
#guard (oR []) == some zero

end Test

end Recal

/-- Exported name (the reading the recalibrated table is to be built from). -/
def oR (m : BMS.Matrix) : Option TM.Term := Recal.oR m


namespace Recal

/-! ## 6. THE EQUATIONAL LAYER — first brick

`plan/constitutions.md` S3 records what this file was: 24 `#guard`s and **zero theorems**, so no fact
quantified over a parameter could be proved on the `oR` side at all.  Validation at points is not
an API.  This is the first equation.

`ofMatrix` is the parser at the bottom of `oR = (1 + ·) ∘ dict ∘ transPort ∘ ofMatrix`, so it is
where an equational layer has to start.  The `#guard`s below include the two degenerate cases and
a malformed-height case, because the raw `Matrix = List (List Nat)` type admits columns this
parser rejects — `lean/scripts/reader_agreement.lean` found that the hard way.

NOT ON THE CRITICAL PATH FOR THE TABLE.  `Certified` never mentions a reader, so the certificate
side does not need this; it is needed by E1-shaped statements quantified over `n`.
-/

def ofMatrixAppendRhs (M N : BMS.Matrix) : Option PS :=
  if M.isEmpty then ofMatrix N
  else if N.isEmpty then ofMatrix M
  else (ofMatrix M).bind fun p => (ofMatrix N).map fun q => p ++ q

#guard ofMatrix ([[0, 0], [1, 1]] ++ [[2, 0]]) ==
  ofMatrixAppendRhs [[0, 0], [1, 1]] [[2, 0]]
#guard ofMatrix (([] : BMS.Matrix) ++ [[0, 0], [1, 1]]) ==
  ofMatrixAppendRhs [] [[0, 0], [1, 1]]
#guard ofMatrix ([[0, 0], [1, 1]] ++ []) ==
  ofMatrixAppendRhs [[0, 0], [1, 1]] []
#guard ofMatrix ([[0, 0, 7]] ++ [[1, 1]]) ==
  ofMatrixAppendRhs [[0, 0, 7]] [[1, 1]]
#guard ofMatrix ([[0, 0]] ++ [[1, 1, 7]]) ==
  ofMatrixAppendRhs [[0, 0]] [[1, 1, 7]]

theorem ofMatrix_append (M N : BMS.Matrix) :
    ofMatrix (M ++ N) = ofMatrixAppendRhs M N := by
  cases M with
  | nil => rfl
  | cons m M =>
    cases N with
    | nil =>
      rw [List.append_nil]
      rfl
    | cons n N =>
      unfold ofMatrixAppendRhs ofMatrix
      simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and,
        List.all_append, List.map_append]
      cases hM : (m :: M).all (fun c => decide (c.length ≤ 2)) <;>
      cases hN : (n :: N).all (fun c => decide (c.length ≤ 2)) <;>
      simp

end Recal

end Trans
