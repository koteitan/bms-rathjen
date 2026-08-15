import Evidence.Region
import Evidence.SqV
/-
Evidence/RegionV.lean — THE VALUE SIDE OF THE REGION BELOW ε_ω

`Evidence/Region.lean` names the region and proves it closed under `BMS.expand`.  This
file gives the region's VALUE in 𝔗(M) and its NORMAL FORM, and measures what is left for
`certIn_region`'s three supplies.

THE VALUE IS ONE CLAUSE.  Reading the index as a Buchholz term, ψ₀(ξ) with ξ = Ω·k ⊕ η
(η being Ω-free) has value

    sumVal (ψ₀ ξ)  =  ω^( ε_{k-1} ⊕ sumVal η )      k ≥ 1
    sumVal (ψ₀ ξ)  =  ω^( sumVal η )                k = 0

with `ω^·` the repo's own `TM.Term.omegaNF` — [Rathjen, 1991] 2.6(vii), the NORMALIZED
Veblen function, which is where the fixed-point re-counting lives.  There is no `φ̄`
recursion, no `isFP` split and no collapsing clause: §16.5 refuted all three as clauses of
a `φ̄`-shaped `sqv`, and in Buchholz coordinates they are `omegaNF`'s own business.  That
is the same sentence as `Evidence/Region.lean`'s, on the value side.

THE NORMAL FORM IS BUCHHOLZ'S, AND IT HAS TWO HALVES.  `nf` asks

  (1) the summands descend — Ω before every ψ₀, and ψ₀(b) after ψ₀(a) only when b ≤ a;
  (2) `ψ₀(a)` is a normal form only when every ψ₀-argument inside `a` is `< a`
      — Buchholz's `a ∈ C₀(a)`.

HALF (2) WAS NOT GUESSED, IT WAS FORCED BY A MEASUREMENT.  With only half (1), the corpus
has 20 indices and `sumVal` is NOT injective on them: `ψ₀(ψ₀(Ω))` and `ψ₀(Ω)` both take the
value ε₀, because ω^ε₀ = ε₀.  Two matrices, one value — exactly the defect §K3.2 records
for `sqv'`, arriving here from the other direction.  Half (2) rejects `ψ₀(ψ₀(Ω))` (its
argument's ψ₀-argument is Ω, and Ω is not `< ψ₀(Ω)`), leaves 18, and `sumVal` is injective
on those.

WHAT THE MEASUREMENTS SAY, on all 18 (the `#guard`s at the end):

    sumVal = oR                                 18/18   the value is the reader's
    fs preserves nf                             18/18   `Hclosed` on the value side
    sumVal injective                            18/18   `Val` is single-valued
    inT (sumVal t)                              18/18   the gate's own guard
    lt (val (fs t n)) (val t), and increasing   18/18   `Hlim` clauses 1 and 2
    BMS.kind agrees with the index's kind        18/18  what the three supplies dispatch on

AND THE SEQUENCE FUNCTION IS STILL THIS REGION'S OWN.  §25.1 of `Evidence/SqV.lean`
measured that no existing sequence tracks expansion; on this region, restricted to the
normal forms — which is the population that measurement should have been taken on — the
two closest are within ONE case each:

    fsN at shift 1     1 of 18 differs      the ε₁ row
    fsV at shift 0     1 of 18 differs      ψ₀(Ω+ω)

Both survivors are genuine: at ε₁, `fsN`'s tower climbs over ω^(ε₀+1) and the matrix's
over ε₀·2; at ψ₀(Ω+ω), `fsV` skips ε₀+1.  An index shift is harmless to the four clauses
(monotonicity carries the cofinality clause across it), so what is owed for `Hlim`'s
fourth conjunct is a DOMINATION against one of these — `Evidence/WF.lean` §15.39's
`limClauses_transfer` — and not a new sequence.  That, plus `Hzero`/`Hsucc`, is the whole
remaining distance to the ε₁ and ε_ω rows' ✅.
-/

namespace Evidence.Region

open BMS TM Term

/-! ## §7 The value -/

/-- `ε_j = φ̄(1,j)`。 -/
def epsT (j : Nat) : Term := phi one (ofNat j)

/-- 引数の先頭に並ぶ Ω の個数。 -/
def omN : A → Nat
  | .nil => 0
  | .om r => omN r + 1
  | .ps r _ => omN r

/-- 添字の値。`ψ₀(Ω·k ⊕ η) = ω^(ε_{k-1} ⊕ η)`、`ω^·` は `omegaNF`。 -/
def sumVal : A → Term
  | .nil => zero
  | .om r => sumVal r
  | .ps r a => plus (sumVal r) (omegaNF
      (if omN a = 0 then sumVal a else plus (epsT (omN a - 1)) (sumVal a)))

/-- 引数として読んだときの値 (Ω の段を ε に読み替える)。 -/
def argVal (a : A) : Term :=
  if omN a = 0 then sumVal a else plus (epsT (omN a - 1)) (sumVal a)

theorem sumVal_ps (r a : A) : sumVal (.ps r a) = plus (sumVal r) (omegaNF (argVal a)) := rfl

/-! ## §8 The normal form -/

/-- 和の最後の (= 最小の) 加数。`some none` は Ω、`some (some a)` は `ψ₀(a)`。 -/
def lastSm : A → Option (Option A)
  | .nil => none
  | .om _ => some none
  | .ps _ a => some (some a)

/-- 和の最初の (= 最大の) `ψ₀` 加数の引数。Ω しかなければ `none`。 -/
def firstArg : A → Option A
  | .nil => none
  | .om r => firstArg r
  | .ps r a => match firstArg r with | some b => some b | none => some a

/-- **Buchholz の標準形。** 加数が降順で、かつ `ψ₀(a)` の中の `ψ₀` 引数が `a` 未満。 -/
def nf : A → Bool
  | .nil => true
  | .om r => nf r && (match lastSm r with
      | none => true | some none => true | some (some _) => false)
  | .ps r a => nf r && nf a
      && (match lastSm r with
          | none => true | some none => true
          | some (some b) => BMS.cmpM (mat a 0) (mat b 0) != .gt)
      && (match firstArg a with
          | none => true | some b => BMS.cmpM (mat b 0) (mat a 0) == .lt)

/-! ## §9 The measurements

The corpus is `Evidence/Region.lean`'s: every top-level index of size ≤ 3, 91 of them,
of which 18 are normal forms. -/

/-- 標準形の添字。 -/
def corpusNF : List A := corpus.filter nf

#guard corpusNF.length == 18

-- 値は reader のものと一致する。
#guard corpusNF.all fun t => Trans.oR (mat t 0) == some (sumVal t)
-- `fs` は標準形を保つ (`Hclosed` の値側)。
#guard corpusNF.all fun t => (List.range 6).all fun n => nf (fs t n)
-- 値は一対一 (`Val` が一価)。
#guard corpusNF.all fun t => (corpusNF.filter fun u => sumVal u == sumVal t).length == 1
-- 値は 𝔗(M) の項 (ゲート自身の番人)。
#guard corpusNF.all fun t => inT (sumVal t) == true
-- 極限節の第 1・第 2 連言。
#guard corpusNF.all fun t => (List.range 5).all fun n =>
  BMS.kind (mat t 0) != BMS.Kind.lim ||
    (lt (sumVal (fs t n)) (sumVal t) && lt (sumVal (fs t n)) (sumVal (fs t (n + 1))))
-- 行列の種別は添字の種別と一致する。
#guard corpusNF.all fun t => BMS.kind (mat t 0) == kindA t

/-- 既存の列関数との差 — 母集団は標準形 18 個。 -/
def seqMiss (f : Term → Nat → Term) (sh : Nat) : Nat :=
  (corpusNF.filter fun t =>
    !((List.range 5).all fun n => sumVal (fs t n) == f (sumVal t) (n + sh))).length

#guard seqMiss Term.fsN 1 == 1
#guard seqMiss Evidence.SqV.fsV 0 == 1
#guard seqMiss Term.fsN 0 == 13
#guard seqMiss Evidence.SqV.fsV 1 == 13

-- ε₁ の行の添字は標準形。
#guard nf (.ps .nil (omPow 2))
-- ε_k の行の添字も標準形。
#guard (List.range 5).all fun k => nf (.ps .nil (omPow (k + 1)))
-- そして ε₁ の行の値は表が主張する `φ̄(1,1)`。
#guard sumVal (.ps .nil (omPow 2)) == phi one one
-- ε_k の行の値は `φ̄(1,k)`。
#guard (List.range 5).all fun k => sumVal (.ps .nil (omPow (k + 1))) == epsT k

end Evidence.Region
