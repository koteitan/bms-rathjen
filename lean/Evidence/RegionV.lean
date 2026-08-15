import Evidence.Region
import Evidence.CNVOps
import Trans.Recal
import TM.FS
/-
Evidence/RegionV.lean — THE VALUE SIDE OF THE REGION BELOW ε_ω

`Evidence/Region.lean` names the region and proves it closed under `BMS.expand`.  This
file gives the region's VALUE in 𝔗(M) and its NORMAL FORM, and measures what is left for
`certIn_region`'s three supplies.  It imports only `Region`, `Trans.Recal` and `TM.FS`, so
that `Evidence/Cert.lean` — where the region's certificate will be assembled — can import
it; the `fsV` half of §9's comparison lives in `Evidence/RegionSeq.lean` because
`Evidence/SqV.lean` imports `Cert.lean` and the arrow must not reverse.

THE VALUE IS ONE CLAUSE.  Reading the index as a Buchholz term, ψ₀(ξ) with ξ = Ω·k ⊕ η
(η being Ω-free) has value

    sumVal (ψ₀ ξ)  =  ω^( ε_{k-1} ⊕ sumVal η )      k ≥ 1
    sumVal (ψ₀ ξ)  =  ω^( sumVal η )                k = 0

with `ω^·` the repo's own `TM.Term.omegaNF` — [Rathjen, 1991] 2.6(vii), the NORMALIZED
Veblen function, which is where the fixed-point re-counting lives.  There is no `φ̄`
recursion, no `isFP` split and no collapsing clause: §16.5 refuted all three as clauses of
a `φ̄`-shaped `sqv`, and in Buchholz coordinates they are `omegaNF`'s own business.  That
is the same sentence as `Evidence/Region.lean`'s, on the value side.

THE COMPARISON MUST BE THE MATRIX'S, NOT THE VALUE'S (§9.1).  Writing `nf`'s two
comparisons with 𝔗(M)'s `le`/`lt` on `argVal` gives a DIFFERENT predicate: `argVal` sends
`Ω` to `ε_{k-1}` and so forgets the level, and at `ψ₀(ψ₀(Ω) ⊕ ψ₀(0))` it accepts what
Buchholz rejects.  The two agree on all 1614 indices of the closure corpus and the
counterexample sits just outside it.

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
    fsV at shift 0     1 of 18 differs      ψ₀(Ω+ω)     (`Evidence/RegionSeq.lean`)

Both survivors are genuine: at ε₁, `fsN`'s tower climbs over ω^(ε₀+1) and the matrix's
over ε₀·2; at ψ₀(Ω+ω), `fsV` skips ε₀+1.  An index shift is harmless to the four clauses
(monotonicity carries the cofinality clause across it), so what is owed for `Hlim`'s
fourth conjunct is a DOMINATION against one of these — `Evidence/WF.lean` §15.39's
`limClauses_transfer` — and not a new sequence.

WHAT IS PROVED HERE, AND WHAT IS LEFT.  §11 proves the value is ALWAYS `CNV` — no normal
form needed, because `Evidence/CNVOps.lean` closes `CNV` under the only two operations
`sumVal` uses.  §12 discharges `certIn_region`'s FIRST TWO SUPPLIES as theorems.  What
remains for the ε₁ and ε_ω rows' ✅ is `Hclosed` (that `fs` preserves `nf`, measured), and
`Hlim` — of whose six conjuncts §9 measures five clean and the sixth is the cofinality
above.
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

/-- **Buchholz の標準形。** 加数が降順で、かつ `ψ₀(a)` の中の `ψ₀` 引数が `a` 未満。
    比較は **行列の辞書式順序** `BMS.cmpM` で書く。§9.1 が、値 `argVal` で書いた
    `nfV` はこれと同じ述語では **ない** ことを反例つきで示す。 -/
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

/-- 同じ形を **値の順序** で書いたもの。§9.1 の反例により `nf` とは別の述語である。 -/
def nfV : A → Bool
  | .nil => true
  | .om r => nfV r && (match lastSm r with
      | none => true | some none => true | some (some _) => false)
  | .ps r a => nfV r && nfV a
      && (match lastSm r with
          | none => true | some none => true
          | some (some b) => le (argVal a) (argVal b))
      && (match firstArg a with
          | none => true | some b => lt (argVal b) (argVal a))

/-! ## §9 The measurements

The corpus is `Evidence/Region.lean`'s: every top-level index of size ≤ 3, 91 of them,
of which 18 are normal forms. -/

/-- 標準形の添字。 -/
def corpusNF : List A := corpus.filter nf

#guard corpusNF.length == 18

/-- 展開で 3 段閉じた、はるかに広い母集団 (1614 個)。 -/
def closureCorpus : List A :=
  let d1 := corpus ++ corpus.flatMap (fun t => (List.range 4).map (fun n => fs t n))
  let d2 := d1 ++ d1.flatMap (fun t => (List.range 4).map (fun n => fs t n))
  (d2 ++ d2.flatMap (fun t => (List.range 3).map (fun n => fs t n))).eraseDups

#guard closureCorpus.length == 1614
#guard (closureCorpus.filter nf).length == 294
-- 広い母集団でも `fs` は標準形を保ち、値は reader と一致する。
#guard (closureCorpus.filter nf).all fun t => (List.range 5).all fun n => nf (fs t n)
#guard (closureCorpus.filter nf).all fun t => Trans.oR (mat t 0) == some (sumVal t)

/-! ### §9.1 THE NORMAL FORM CANNOT BE WRITTEN IN THE VALUE'S ORDER

`nfV` is `nf` with both comparisons moved from `BMS.cmpM` to 𝔗(M)'s `le`/`lt` on `argVal`.
That would have been worth having: the limit clause's first conjunct is a 𝔗(M) inequality,
so one order would have served both obligations.  **It is a different predicate, and the
value's order is the wrong one.**

    on all 1614 indices of `closureCorpus`   `nf` and `nfV` agree
    at `ψ₀(ψ₀(Ω) ⊕ ψ₀(0))`                   `nf` = false, `nfV` = TRUE

WHY, IN ONE LINE.  `argVal` sends `Ω` to `ε_{k-1}`, so it FORGETS THE LEVEL.  Buchholz's
condition at that index asks whether `Ω < ψ₀(Ω) ⊕ ψ₀(0)`, and the answer is no; `nfV` asks
whether `ε₀ < ε₀ ⊕ 1`, and the answer is yes.  The matrix's lexicographic order keeps the
level in row 1 and gets it right.  `nfV` also FAILS TO BE CLOSED under `fs` at that index —
all four of its expansions are rejected by both predicates — which is how the defect
announced itself.

AND THE AGREEMENT ON 1614 WAS NOT ENOUGH.  The corpus is the size-≤3 indices closed under
`fs` three times; the counterexample sits just outside it, and the definition had already
been switched on the strength of that agreement.  Same shape as this repo's earlier
corpus accidents: **a measurement over a population we generated is a measurement about
the population.** -/

def cexNF : A := .ps .nil (.ps (.ps .nil (.om .nil)) .nil)

#guard nf cexNF == false
#guard nfV cexNF == true
#guard closureCorpus.all fun t => nf t == nfV t
#guard !(closureCorpus.contains cexNF)
-- `nfV` の側は `fs` で閉じない。
#guard (List.range 4).all fun n => nfV (fs cexNF n) == false

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
#guard seqMiss Term.fsN 0 == 13
-- `fsV` の方は `Evidence/RegionSeq.lean` にある (`SqV.lean` は `Cert.lean` を import する
-- ので、証明側から見える位置には置けない)。

-- ε₁ の行の添字は標準形。
#guard nf (.ps .nil (omPow 2))
-- ε_k の行の添字も標準形。
#guard (List.range 5).all fun k => nf (.ps .nil (omPow (k + 1)))
-- そして ε₁ の行の値は表が主張する `φ̄(1,1)`。
#guard sumVal (.ps .nil (omPow 2)) == phi one one
-- ε_k の行の値は `φ̄(1,k)`。
#guard (List.range 5).all fun k => sumVal (.ps .nil (omPow (k + 1))) == epsT k

/-! ## §10 The zero and successor supplies

`certIn_region`'s first two supplies ask what the value is when `BMS.kind S` is `zero` or
`succ`.  `Region.kind_mat` says which index that is — `nil` and `ps r nil` — so both
supplies reduce to two equations about `sumVal`.  `omegaNF zero = 1` is the whole content
of the successor one: the last summand `ψ₀(0)` contributes exactly `1`, so a successor
index's value is `sumVal r ⊕ 1` with `sumVal r` the value of its own expansion. -/

theorem kindA_zero {t : A} (h : kindA t = BMS.Kind.zero) : t = .nil := by
  cases t with
  | nil => rfl
  | om _ => exact BMS.Kind.noConfusion h
  | ps r a => cases a with
    | nil => exact BMS.Kind.noConfusion h
    | om _ => exact BMS.Kind.noConfusion h
    | ps _ _ => exact BMS.Kind.noConfusion h

theorem kindA_succ {t : A} (h : kindA t = BMS.Kind.succ) : ∃ r, t = .ps r .nil := by
  cases t with
  | nil => exact BMS.Kind.noConfusion h
  | om _ => exact BMS.Kind.noConfusion h
  | ps r a => cases a with
    | nil => exact ⟨r, rfl⟩
    | om _ => exact BMS.Kind.noConfusion h
    | ps _ _ => exact BMS.Kind.noConfusion h

theorem sumVal_nil : sumVal .nil = zero := rfl

/-- `ω^0 = 1` — 最後の加数 `ψ₀(0)` はちょうど `1` を出す。 -/
theorem omegaNF_zero : omegaNF zero = one := by decide

/-- **後続の値。** 最後の加数が `ψ₀(0)` なら値は `sumVal r ⊕ 1`。 -/
theorem sumVal_succ (r : A) : sumVal (.ps r .nil) = plus (sumVal r) one := by
  rw [sumVal_ps]
  exact congrArg (plus (sumVal r)) omegaNF_zero

/-- 後続の添字の展開はその前身。 -/
theorem fs_succ (r : A) (n : Nat) : fs (.ps r .nil) n = r := rfl

/-- 標準形は部分添字に遺伝する。 -/
theorem nf_of_ps {r a : A} (h : nf (.ps r a) = true) : nf r = true ∧ nf a = true := by
  have h1 : (nf r && nf a
      && (match lastSm r with
          | none => true | some none => true
          | some (some b) => BMS.cmpM (mat a 0) (mat b 0) != .gt)
      && (match firstArg a with
          | none => true | some b => BMS.cmpM (mat b 0) (mat a 0) == .lt)) = true := h
  have h2 := (Bool.and_eq_true _ _).mp h1
  have h3 := (Bool.and_eq_true _ _).mp h2.1
  exact (Bool.and_eq_true _ _).mp h3.1

theorem topOK_of_ps {r a : A} (h : topOK (.ps r a) = true) : topOK r = true := h

/-! ## §11 The value is always `CNV`

`Evidence/CNVOps.lean` gives `CNV` closed under `plus` and `ω^·`, which is exactly what
`sumVal` is built from — so this needs no normal form at all, and the `#guard` over all 91
indices was measuring a theorem.  It supplies `hfc` for `limClauses_transfer`, `inT` for the
gate's guard, and `CNV` for `asm_veblen`. -/

open Evidence.WF (CNV cnv_plus cnv_omegaNF cnv_ofNat inT_of_cnv)

theorem cnv_one : CNV one = true := rfl

theorem cnv_epsT (j : Nat) : CNV (epsT j) = true := by
  show (CNV one && CNV (ofNat j)) = true
  rw [cnv_one, cnv_ofNat j]
  rfl

/-- **領域の値はつねに `CNV`。** 標準形はいらない。 -/
theorem cnv_sumVal : ∀ (t : A), CNV (sumVal t) = true := by
  intro t
  induction t with
  | nil => rfl
  | om r ih => exact ih
  | ps r a ihr iha =>
    rw [sumVal_ps]
    refine cnv_plus ihr (cnv_omegaNF ?_)
    show CNV (if omN a = 0 then sumVal a else plus (epsT (omN a - 1)) (sumVal a)) = true
    by_cases h : omN a = 0
    · rw [if_pos h]; exact iha
    · rw [if_neg h]; exact cnv_plus (cnv_epsT _) iha

/-- 値は 𝔗(M) の項 — ゲート自身の番人。 -/
theorem inT_sumVal (t : A) : inT (sumVal t) = true := inT_of_cnv _ (cnv_sumVal t)

/-! ## §12 THE FIRST TWO SUPPLIES, DISCHARGED

`Reg`/`Val` are `certIn_region`'s two parameters at this region, and `Hzero`/`Hsucc` are
now theorems.  Both go through `Region.kind_mat`: a kind-zero matrix comes only from the
index `nil`, whose value is `0`; a kind-succ matrix comes only from `ps r nil`, whose value
is `sumVal r ⊕ 1` and whose every expansion is `mat r 0` — the SAME matrix for every `n`,
which is what `Certified.succ` wants.

`Hlim` is what remains, and of its six conjuncts §9 measures five clean; the sixth is
cofinality, for which the route is `Evidence/WF.lean` §15.39's `limClauses_transfer`. -/

/-- 領域: 標準形の最上位添字の行列。 -/
def Reg (S : BMS.Matrix) : Prop := ∃ t, nf t = true ∧ topOK t = true ∧ S = mat t 0

/-- その上の値付け。 -/
def Val (S : BMS.Matrix) (v : Term) : Prop :=
  ∃ t, nf t = true ∧ topOK t = true ∧ S = mat t 0 ∧ v = sumVal t

/-- **`Hzero`。** 種別 0 の行列は添字 `nil` から来て、値は `0`。 -/
theorem hzero_supply : ∀ (S : BMS.Matrix) (v : Term), Reg S → Val S v →
    BMS.kind S = BMS.Kind.zero → v = zero := by
  rintro S v _ ⟨t, hnf, htop, rfl, rfl⟩ hk
  rw [kind_mat t htop] at hk
  rw [kindA_zero hk]
  rfl

/-- **`Hsucc`。** 種別後続の行列は `ps r nil` から来て、値は `sumVal r ⊕ 1`。 -/
theorem hsucc_supply : ∀ (S : BMS.Matrix) (v : Term), Reg S → Val S v →
    BMS.kind S = BMS.Kind.succ →
    ∃ u, v = plus u one ∧ inT v = true ∧ inT u = true ∧ lt u v = true
         ∧ ∀ n, Val (BMS.expand S n) u := by
  rintro S v _ ⟨t, hnf, htop, rfl, rfl⟩ hk
  rw [kind_mat t htop] at hk
  obtain ⟨r, rfl⟩ := kindA_succ hk
  refine ⟨sumVal r, sumVal_succ r, inT_sumVal _, inT_sumVal _, ?_, ?_⟩
  · rw [sumVal_succ r, Evidence.WF.plus_one_eq_succT (sumVal r) (cnv_sumVal r)]
    exact Evidence.WF.lt_succT (sumVal r) (cnv_sumVal r)
  · intro n
    refine ⟨r, (nf_of_ps hnf).1, topOK_of_ps htop, ?_, rfl⟩
    show (BMS.expand? (mat (.ps r .nil) 0) n).getD [] = mat r 0
    rw [expand_mat (.ps r .nil) htop (by intro h; exact A.noConfusion h) n]
    rfl

end Evidence.Region
