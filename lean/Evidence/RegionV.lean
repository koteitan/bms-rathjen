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
`sumVal` uses.  §12 discharges `certIn_region`'s FIRST TWO SUPPLIES as theorems.  §13
proves `Hclosed` — **the region is closed under `BMS.expand`, unconditionally** — the last
case, `CaseThree`, being closed in §13.7 by a length argument.

§14 then reduces `Hlim` itself to TWO named holes, `ArgLim` and `PrefixLim` — the four
clauses for one principal term and its sequence, and the fact that a fixed prefix on the
left preserves them.  The associativity of `plus` that reduction needed is now proved
(`Evidence/CNVOps.lean` §19).

`PrefixLim` — `LimClauses V g → LimClauses (P ⊕ V) (fun n => P ⊕ g n)` — is now PROVED
(`Evidence/CNVOps.lean` §23), with no side condition.

§15 then shows `ArgLim` is itself a RECURSION: the third case of `fsP` reduces to the inner
`ArgLim` plus that same prefix combinator.  So the ✅ is THREE BASE FACTS away, one per case
of `fsP`, and `Evidence/WF.lean` has one combinator aimed at each:

    ArgLimRep   last summand `ψ₀(0)`   — sequence `ψ₀(b)·(n+1)`, combinator (A)
    ArgLimOm    last summand `Ω`       — sequence the Ω-tower, combinator (B)
    ArgLimLift  the `ω^·` step only

and §15.4 shows the third is not combinator (C) after all but `OmegaLim` — that `ω^·`
preserves the four clauses — because 2 of its 69 sequence members are ones `omegaNF`
re-counts, and `φ̄(0,y)` is a different ordinal from `ω^y` exactly there.
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

/-- `t` の中の **すべての** `ψ₀` 引数が `B` 未満か。 -/
def argsLtM (B : Matrix) : A → Bool
  | .nil => true
  | .om r => argsLtM B r
  | .ps r a => argsLtM B r && (BMS.cmpM (mat a 0) B == .lt) && argsLtM B a

/-- 加数が降順か (直前の加数との比較)。 -/
def descOK (r a : A) : Bool :=
  match lastSm r with
  | none => true | some none => true
  | some (some b) => BMS.cmpM (mat a 0) (mat b 0) != .gt

/-- Ω は Ω の後ろにしか置けない。 -/
def omOK (r : A) : Bool :=
  match lastSm r with | none => true | some none => true | some (some _) => false

/-- `ψ₀(a)` が Buchholz の標準形か — `a ∈ C₀(a)`、すなわち `a` の中のどの `ψ₀`
    引数も `a` 未満。 -/
def fpOK (a : A) : Bool := argsLtM (mat a 0) a

/-- **Buchholz の標準形。** 加数が降順で、どの `ψ₀` 節も `a ∈ C₀(a)` を満たす。
    比較は **行列の辞書式順序** `BMS.cmpM` で書く。§9.1 が、値 `argVal` で書いた
    `nfV` はこれと同じ述語では **ない** ことを反例つきで示す。 -/
def nf : A → Bool
  | .nil => true
  | .om r => nf r && omOK r
  | .ps r a => nf r && nf a && descOK r a && fpOK a

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

/-! ### §9.2 THE TWO ROWS' VALUES ARE THEOREMS, NOT GUARDS

A `#guard` is a computation on a closed term; the certificate has to cite an EQUATION.
These are the two the registry would name.  They need no normal form, no `oR`, and no part
of §13 — so what a ✅ on these rows would assert about the VALUE is already fixed, and only
the CERTIFICATE is outstanding. -/

theorem omN_omPow : ∀ (k : Nat), omN (omPow k) = k
  | 0 => rfl
  | k + 1 => by show omN (omPow k) + 1 = k + 1; rw [omN_omPow k]

theorem sumVal_omPow : ∀ (k : Nat), sumVal (omPow k) = zero
  | 0 => rfl
  | k + 1 => by show sumVal (omPow k) = zero; exact sumVal_omPow k

theorem sumVal_omPow_succ : ∀ (k : Nat), sumVal (.ps .nil (omPow (k + 1))) = epsT k := by
  intro k
  show plus (sumVal .nil) (omegaNF (argVal (omPow (k + 1)))) = epsT k
  have hom : omN (omPow (k + 1)) = k + 1 := omN_omPow (k + 1)
  have hsum : sumVal (omPow (k + 1)) = zero := sumVal_omPow (k + 1)
  show plus zero (omegaNF (if omN (omPow (k + 1)) = 0 then sumVal (omPow (k + 1))
    else plus (epsT (omN (omPow (k + 1)) - 1)) (sumVal (omPow (k + 1))))) = epsT k
  rw [hom, if_neg (by omega), hsum, show (k + 1 - 1) = k from rfl]
  show plus zero (omegaNF (plus (epsT k) zero)) = epsT k
  rw [show plus (epsT k) zero = epsT k from rfl]
  show plus zero (omegaNF (phi one (ofNat k))) = phi one (ofNat k)
  rfl

/-- **ε₁ の行の値。** 表が主張する `φ̄(1,1)` に等しい。 -/
theorem sumVal_eps1 : sumVal (.ps .nil (omPow 2)) = phi one one := sumVal_omPow_succ 1

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
  have h1 : (nf r && nf a && descOK r a && fpOK a) = true := h
  have h2 := (Bool.and_eq_true _ _).mp h1
  have h3 := (Bool.and_eq_true _ _).mp h2.1
  exact (Bool.and_eq_true _ _).mp h3.1

theorem topOK_of_ps {r a : A} (h : topOK (.ps r a) = true) : topOK r = true := h

/-! ## §11 The value is always `CNV`

`Evidence/CNVOps.lean` gives `CNV` closed under `plus` and `ω^·`, which is exactly what
`sumVal` is built from — so this needs no normal form at all, and the `#guard` over all 91
indices was measuring a theorem.  It supplies `hfc` for `limClauses_transfer`, `inT` for the
gate's guard, and `CNV` for `asm_veblen`. -/

open Evidence.WF (CNV cnv_plus cnv_omegaNF cnv_ofNat inT_of_cnv plus_assoc LimClauses
  lim_clauses_prefix isAP_omegaNF plus_zero_left DnFacts omegaNF_mono isAP_hdOf
  omegaNF_ne_zero)

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

/-! ## §13 TOWARD `Hclosed` — the algebra of `argsLtM`

`nf` is a conjunction of local conditions at each node, and `fs t n` replaces `t`'s last
summand `ψ₀(a)` by `fsP a n`.  So closure splits into: the untouched prefix (free), the
junction (transitivity of `cmpM`), and `nf (fsP a n)`.

The one non-obvious step is RESTRICTION.  `fpOK (ps b c)` bounds `b`'s arguments by
`mat (ps b c) 0 = mat b 0 ++ Z`, and forming `ψ₀(b)` needs them bounded by `mat b 0`.
`argsLtM_restrict` does that, and its content is `Evidence/CmpM.lean`'s `cmpM_gt_lt_len`:
an argument sitting inside `b` is SHORTER than `b`, so it cannot be `≥ mat b 0` while
being `< mat b 0 ++ Z`. -/

theorem nf_ps_iff {r a : A} : nf (.ps r a) = true ↔
    nf r = true ∧ nf a = true ∧ descOK r a = true ∧ fpOK a = true := by
  constructor
  · intro h
    have h1 : (nf r && nf a && descOK r a && fpOK a) = true := h
    have h2 := (Bool.and_eq_true _ _).mp h1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    have h4 := (Bool.and_eq_true _ _).mp h3.1
    exact ⟨h4.1, h4.2, h3.2, h2.2⟩
  · intro ⟨h1, h2, h3, h4⟩
    show (nf r && nf a && descOK r a && fpOK a) = true
    rw [h1, h2, h3, h4]
    rfl

theorem nf_om_iff {r : A} : nf (.om r) = true ↔ nf r = true ∧ omOK r = true := by
  constructor
  · intro h; exact (Bool.and_eq_true _ _).mp h
  · intro ⟨h1, h2⟩; show (nf r && omOK r) = true; rw [h1, h2]; rfl

theorem argsLtM_app (B : Matrix) : ∀ (s r : A),
    argsLtM B (app r s) = (argsLtM B r && argsLtM B s) := by
  intro s
  induction s with
  | nil => intro r; show argsLtM B r = (argsLtM B r && true); rw [Bool.and_true]
  | om s ih => intro r; show argsLtM B (app r s) = _; rw [ih r]; rfl
  | ps s a ih _ =>
    intro r
    show (argsLtM B (app r s) && (BMS.cmpM (mat a 0) B == .lt) && argsLtM B a) = _
    rw [ih r]
    show ((argsLtM B r && argsLtM B s) && (BMS.cmpM (mat a 0) B == .lt) && argsLtM B a)
      = (argsLtM B r && (argsLtM B s && (BMS.cmpM (mat a 0) B == .lt) && argsLtM B a))
    rw [Bool.and_assoc, Bool.and_assoc, Bool.and_assoc]

/-- 上界を上げても成り立つ。 -/
theorem argsLtM_mono {B B' : Matrix} (h : (BMS.cmpM B B' != Ordering.gt) = true) :
    ∀ (t : A), argsLtM B t = true → argsLtM B' t = true := by
  have key : ∀ X, (BMS.cmpM X B == Ordering.lt) = true → (BMS.cmpM X B' == Ordering.lt) = true := by
    intro X hX
    have hXB : BMS.cmpM X B = Ordering.lt := by
      cases hc : BMS.cmpM X B with
      | lt => rfl
      | eq => rw [hc] at hX; exact Bool.noConfusion hX
      | gt => rw [hc] at hX; exact Bool.noConfusion hX
    cases hBB : BMS.cmpM B B' with
    | gt => rw [hBB] at h; exact Bool.noConfusion h
    | lt => rw [BMS.cmpM_trans X B B' hXB hBB]; rfl
    | eq => rw [← BMS.cmpM_eq B B' hBB, hXB]; rfl
  intro t
  induction t with
  | nil => intro _; rfl
  | om r ih => exact ih
  | ps r a ihr iha =>
    intro ht
    have h1 : (argsLtM B r && (BMS.cmpM (mat a 0) B == .lt) && argsLtM B a) = true := ht
    have h2 := (Bool.and_eq_true _ _).mp h1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    show (argsLtM B' r && (BMS.cmpM (mat a 0) B' == .lt) && argsLtM B' a) = true
    rw [ihr h3.1, key _ h3.2, iha h2.2]
    rfl

/-- 短いものは、接尾辞を切っても下にとどまる。 -/
theorem cmpM_lt_restrict {X B Z : Matrix} (hlen : X.length < B.length)
    (h : BMS.cmpM X (B ++ Z) = Ordering.lt) : BMS.cmpM X B = Ordering.lt := by
  cases hc : BMS.cmpM X B with
  | lt => rfl
  | eq => exact absurd (congrArg List.length (BMS.cmpM_eq X B hc)) (by omega)
  | gt => exact absurd (BMS.cmpM_gt_lt_len X B Z hc h) (by omega)

/-- **上界を接頭辞へ制限する。** -/
theorem argsLtM_restrict (B Z : Matrix) : ∀ (t : A), len t ≤ B.length →
    argsLtM (B ++ Z) t = true → argsLtM B t = true := by
  intro t
  induction t with
  | nil => intro _ _; rfl
  | om r ih =>
    intro hl ht
    have hl' : len r + 1 ≤ B.length := hl
    exact ih (by omega) ht
  | ps r a ihr iha =>
    intro hl ht
    have hl' : len r + len a + 1 ≤ B.length := hl
    have h1 : (argsLtM (B ++ Z) r && (BMS.cmpM (mat a 0) (B ++ Z) == .lt)
      && argsLtM (B ++ Z) a) = true := ht
    have h2 := (Bool.and_eq_true _ _).mp h1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    have hlt : BMS.cmpM (mat a 0) (B ++ Z) = Ordering.lt := by
      cases hc : BMS.cmpM (mat a 0) (B ++ Z) with
      | lt => rfl
      | eq => rw [hc] at h3; exact Bool.noConfusion h3.2
      | gt => rw [hc] at h3; exact Bool.noConfusion h3.2
    show (argsLtM B r && (BMS.cmpM (mat a 0) B == .lt) && argsLtM B a) = true
    rw [ihr (by omega) h3.1, iha (by omega) h2.2,
      cmpM_lt_restrict (by rw [mat_len]; omega) hlt]
    rfl

/-- `ψ₀(b ⊕ ψ₀(c))` が標準形なら、`ψ₀(b)` の不動点条件も成り立つ。 -/
theorem fpOK_left_ps {b c : A} (h : fpOK (.ps b c) = true) : fpOK b = true := by
  have h1 : (argsLtM (mat (.ps b c) 0) b && _ && _) = true := h
  have hb := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h1).1).1
  have he : mat (A.ps b c) 0 = mat b 0 ++ ([0, 0] :: mat c 1) := rfl
  rw [he] at hb
  exact argsLtM_restrict (mat b 0) _ b (by rw [mat_len]; exact Nat.le_refl _) hb

theorem fpOK_left_om {b : A} (h : fpOK (.om b) = true) : fpOK b = true := by
  have hb : argsLtM (mat (A.om b) 0) b = true := h
  have he : mat (A.om b) 0 = mat b 0 ++ [[0, 1]] := rfl
  rw [he] at hb
  exact argsLtM_restrict (mat b 0) _ b (by rw [mat_len]; exact Nat.le_refl _) hb

/-! ### §13.1 `Hclosed` at the successor index -/

/-- 後続の添字は前身へ落ちるだけなので、標準形は自明に保たれる。 -/
theorem nf_fs_succ {r : A} (h : nf (.ps r .nil) = true) (n : Nat) :
    nf (fs (.ps r .nil) n) = true := (nf_ps_iff.mp h).1

theorem topOK_fs_succ {r : A} (h : topOK (.ps r .nil) = true) (n : Nat) :
    topOK (fs (.ps r .nil) n) = true := h

/-! ### §13.2 The Ω tower

`nf (om b)` forces `b` to be a run of `Ω`s, and then `iterOm b k` is `ψ₀(towArg b k)` with
`towArg b (k+1) = b ⊕ ψ₀(towArg b k)`.  Everything follows from ONE strictly increasing
chain, `towArg b k < towArg b (k+1)`, which is `cmpM_append_left` plus the depth shift. -/

theorem argsLtM_omPow (B : Matrix) : ∀ (j : Nat), argsLtM B (omPow j) = true
  | 0 => rfl
  | j + 1 => argsLtM_omPow B j

theorem omOK_omPow : ∀ (j : Nat), omOK (omPow j) = true
  | 0 => rfl
  | _ + 1 => rfl

theorem nf_omPow : ∀ (j : Nat), nf (omPow j) = true
  | 0 => rfl
  | j + 1 => by
    show (nf (omPow j) && omOK (omPow j)) = true
    rw [nf_omPow j, omOK_omPow j]
    rfl

theorem descOK_omPow (j : Nat) (a : A) : descOK (omPow j) a = true := by
  cases j with
  | zero => rfl
  | succ _ => rfl

/-- `nf (om b)` は `b` が Ω の列であることを強制する。 -/
theorem om_all : ∀ (b : A), nf (.om b) = true → ∃ j, b = omPow j := by
  intro b
  induction b with
  | nil => intro _; exact ⟨0, rfl⟩
  | om b' ih =>
    intro h
    obtain ⟨hnb, _⟩ := nf_om_iff.mp h
    obtain ⟨j, hj⟩ := ih hnb
    exact ⟨j + 1, by rw [hj]; rfl⟩
  | ps r a _ _ =>
    intro h
    exact absurd (nf_om_iff.mp h).2 (by intro hc; exact Bool.noConfusion hc)

/-- 塔の引数。 -/
def towArg (b : A) : Nat → A
  | 0 => b
  | k + 1 => .ps b (towArg b k)

theorem iterOm_eq (b : A) : ∀ (k : Nat), iterOm b k = .ps .nil (towArg b k)
  | 0 => rfl
  | k + 1 => by
    show A.ps .nil (app b (iterOm b k)) = _
    rw [iterOm_eq b k]
    rfl

theorem mat_towArg_succ (b : A) (k d : Nat) :
    mat (towArg b (k + 1)) d = mat b d ++ ([d, 0] :: mat (towArg b k) (d + 1)) := rfl

/-- **塔は真に増える。** -/
theorem towArg_lt (b : A) : ∀ (k : Nat),
    BMS.cmpM (mat (towArg b k) 0) (mat (towArg b (k + 1)) 0) = Ordering.lt := by
  intro k
  induction k with
  | zero =>
    show BMS.cmpM (mat b 0) (mat b 0 ++ ([0, 0] :: mat (towArg b 0) 1)) = Ordering.lt
    exact BMS.cmpM_prefix_lt _ _ _
  | succ j ih =>
    rw [mat_towArg_succ b j 0, mat_towArg_succ b (j + 1) 0,
      show mat b 0 ++ ([0, 0] :: mat (towArg b j) 1)
        = (mat b 0 ++ [[0, 0]]) ++ mat (towArg b j) 1 from by
        rw [List.append_assoc]; rfl,
      show mat b 0 ++ ([0, 0] :: mat (towArg b (j + 1)) 1)
        = (mat b 0 ++ [[0, 0]]) ++ mat (towArg b (j + 1)) 1 from by
        rw [List.append_assoc]; rfl,
      BMS.cmpM_append_left,
      show (1 : Nat) = 0 + 1 from rfl, cmpM_mat_depth]
    exact ih

/-- 塔の引数はもとの `Ω` 付き引数より小さい。 -/
theorem towArg_lt_om (b : A) : ∀ (k : Nat),
    BMS.cmpM (mat (towArg b k) 0) (mat (.om b) 0) = Ordering.lt := by
  intro k
  cases k with
  | zero =>
    show BMS.cmpM (mat b 0) (mat b 0 ++ [[0, 1]]) = Ordering.lt
    exact BMS.cmpM_prefix_lt _ _ _
  | succ j =>
    rw [mat_towArg_succ b j 0, show mat (A.om b) 0 = mat b 0 ++ [[0, 1]] from rfl,
      BMS.cmpM_append_left]
    rfl

theorem leM_of_lt {X Y : Matrix} (h : BMS.cmpM X Y = Ordering.lt) :
    (BMS.cmpM X Y != Ordering.gt) = true := by rw [h]; rfl

/-- 塔のどの段も標準形で、不動点条件を満たす。 -/
theorem towArg_ok (j : Nat) : ∀ (k : Nat),
    nf (towArg (omPow j) k) = true ∧ fpOK (towArg (omPow j) k) = true := by
  intro k
  induction k with
  | zero => exact ⟨nf_omPow j, argsLtM_omPow _ j⟩
  | succ i ih =>
    refine ⟨nf_ps_iff.mpr ⟨nf_omPow j, ih.1, descOK_omPow j _, ih.2⟩, ?_⟩
    show (argsLtM (mat (towArg (omPow j) (i + 1)) 0) (omPow j)
      && (BMS.cmpM (mat (towArg (omPow j) i) 0)
            (mat (towArg (omPow j) (i + 1)) 0) == Ordering.lt)
      && argsLtM (mat (towArg (omPow j) (i + 1)) 0) (towArg (omPow j) i)) = true
    rw [argsLtM_omPow, towArg_lt,
      argsLtM_mono (leM_of_lt (towArg_lt (omPow j) i)) _ ih.2]
    rfl

/-! ### §13.3 The successor argument, and concatenation -/

theorem lastSm_rep (b : A) : ∀ (n : Nat), lastSm (rep b n) = some (some b)
  | 0 => rfl
  | _ + 1 => rfl

theorem firstSm_rep (b : A) : ∀ (n : Nat), firstSm (rep b n) = some (some b)
  | 0 => rfl
  | k + 1 => by
    show (match firstSm (rep b k) with | some x => some x | none => some (some b)) = _
    rw [firstSm_rep b k]

theorem descOK_rep (b : A) (n : Nat) : descOK (rep b n) b = true := by
  show (match lastSm (rep b n) with
    | none => true | some none => true
    | some (some x) => BMS.cmpM (mat b 0) (mat x 0) != Ordering.gt) = true
  rw [lastSm_rep]
  show (BMS.cmpM (mat b 0) (mat b 0) != Ordering.gt) = true
  rw [BMS.cmpM_refl]
  rfl

theorem nf_rep {b : A} (hb : nf b = true) (hfp : fpOK b = true) :
    ∀ (n : Nat), nf (rep b n) = true
  | 0 => nf_ps_iff.mpr ⟨rfl, hb, rfl, hfp⟩
  | k + 1 => nf_ps_iff.mpr ⟨nf_rep hb hfp k, hb, descOK_rep b k, hfp⟩

theorem argsLtM_rep {b : A} {B : Matrix} (h1 : (BMS.cmpM (mat b 0) B == Ordering.lt) = true)
    (h2 : argsLtM B b = true) : ∀ (n : Nat), argsLtM B (rep b n) = true
  | 0 => by
    show (argsLtM B .nil && (BMS.cmpM (mat b 0) B == Ordering.lt) && argsLtM B b) = true
    rw [h1, h2]; rfl
  | k + 1 => by
    show (argsLtM B (rep b k) && (BMS.cmpM (mat b 0) B == Ordering.lt) && argsLtM B b) = true
    rw [argsLtM_rep h1 h2 k, h1, h2]; rfl

/-- `rep b n` の行列は、最初のブロックのあと `(0,0)` から続く。 -/
theorem mat_rep_split (b : A) : ∀ (n : Nat),
    mat (rep b n) 0 = ([0, 0] :: mat b 1)
    ∨ ∃ U, mat (rep b n) 0 = ([0, 0] :: mat b 1) ++ ([0, 0] :: U)
  | 0 => Or.inl rfl
  | k + 1 => by
    have hstep : mat (rep b (k + 1)) 0 = mat (rep b k) 0 ++ ([0, 0] :: mat b 1) := rfl
    rcases mat_rep_split b k with h | ⟨U, h⟩
    · exact Or.inr ⟨mat b 1, by rw [hstep, h]⟩
    · refine Or.inr ⟨U ++ ([0, 0] :: mat b 1), ?_⟩
      rw [hstep, h, List.append_assoc, List.cons_append]
      rfl

/-- `mat (rep b n) 0` は `ψ₀(b ⊕ 1)` の行列より小さい。 -/
theorem mat_rep_lt (b : A) (n : Nat) :
    BMS.cmpM (mat (rep b n) 0) (mat (.ps .nil (.ps b .nil)) 0) = Ordering.lt := by
  have hR : mat (A.ps .nil (A.ps b .nil)) 0 = ([0, 0] :: mat b 1) ++ [[1, 0]] := rfl
  rw [hR]
  rcases mat_rep_split b n with h | ⟨U, h⟩
  · rw [h]; exact BMS.cmpM_prefix_lt _ _ _
  · rw [h, BMS.cmpM_append_left]
    show (BMS.cmpCol [0, 0] [1, 0]).then (BMS.cmpM U []) = Ordering.lt
    rfl

/-! ### §13.4 Concatenation preserves the normal form -/

/-- `s` を `r` の後ろに置けるか。 -/
def fits (r s : A) : Bool :=
  match firstSm s with
  | none => true
  | some none => omOK r
  | some (some y) => descOK r y

theorem fits_of_firstSm_none {r s : A} (h : firstSm s = none) : fits r s = true := by
  show (match firstSm s with
    | none => true | some none => omOK r | some (some y) => descOK r y) = true
  rw [h]

theorem lastSm_app_ne {r s : A} (h : s ≠ .nil) : lastSm (app r s) = lastSm s := by
  cases s with
  | nil => exact absurd rfl h
  | om _ => rfl
  | ps _ _ => rfl

theorem omOK_app {r s : A} (h : s ≠ .nil) : omOK (app r s) = omOK s := by
  show (match lastSm (app r s) with
    | none => true | some none => true | some (some _) => false)
    = (match lastSm s with
    | none => true | some none => true | some (some _) => false)
  rw [lastSm_app_ne h]

theorem descOK_app {r s a : A} (h : s ≠ .nil) : descOK (app r s) a = descOK s a := by
  show (match lastSm (app r s) with
    | none => true | some none => true
    | some (some x) => BMS.cmpM (mat a 0) (mat x 0) != Ordering.gt)
    = (match lastSm s with
    | none => true | some none => true
    | some (some x) => BMS.cmpM (mat a 0) (mat x 0) != Ordering.gt)
  rw [lastSm_app_ne h]

theorem fits_om {r s' : A} : firstSm s' ≠ none → fits r (.om s') = fits r s' := by
  intro h
  cases hx : firstSm s' with
  | none => exact absurd hx h
  | some x =>
    show (match firstSm (A.om s') with
      | none => true | some none => omOK r | some (some y) => descOK r y)
      = (match firstSm s' with
      | none => true | some none => omOK r | some (some y) => descOK r y)
    rw [show firstSm (A.om s') = some x from by
      show (match firstSm s' with | some y => some y | none => some none) = some x
      rw [hx], hx]

theorem fits_ps {r s' a : A} : firstSm s' ≠ none → fits r (.ps s' a) = fits r s' := by
  intro h
  cases hx : firstSm s' with
  | none => exact absurd hx h
  | some x =>
    show (match firstSm (A.ps s' a) with
      | none => true | some none => omOK r | some (some y) => descOK r y)
      = (match firstSm s' with
      | none => true | some none => omOK r | some (some y) => descOK r y)
    rw [show firstSm (A.ps s' a) = some x from by
      show (match firstSm s' with | some y => some y | none => some (some a)) = some x
      rw [hx], hx]

theorem firstSm_none_iff : ∀ (s : A), firstSm s = none ↔ s = .nil := by
  intro s
  cases s with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | om s' =>
    constructor
    · intro h
      exfalso
      cases hx : firstSm s' with
      | none => rw [show firstSm (A.om s') = some none from by
                  show (match firstSm s' with | some y => some y | none => some none) = some none
                  rw [hx]] at h
                exact absurd h (by simp)
      | some x => rw [show firstSm (A.om s') = some x from by
                    show (match firstSm s' with | some y => some y | none => some none) = some x
                    rw [hx]] at h
                  exact absurd h (by simp)
    · intro h; exact absurd h (by intro hc; exact A.noConfusion hc)
  | ps s' a =>
    constructor
    · intro h
      exfalso
      cases hx : firstSm s' with
      | none => rw [show firstSm (A.ps s' a) = some (some a) from by
                  show (match firstSm s' with | some y => some y | none => some (some a))
                    = some (some a)
                  rw [hx]] at h
                exact absurd h (by simp)
      | some x => rw [show firstSm (A.ps s' a) = some x from by
                    show (match firstSm s' with | some y => some y | none => some (some a))
                      = some x
                    rw [hx]] at h
                  exact absurd h (by simp)
    · intro h; exact absurd h (by intro hc; exact A.noConfusion hc)

/-- **連結は標準形を保つ。** -/
theorem nf_app : ∀ (s r : A), nf r = true → nf s = true → fits r s = true →
    nf (app r s) = true := by
  intro s
  induction s with
  | nil => intro r hr _ _; exact hr
  | om s' ih =>
    intro r hr hs hf
    obtain ⟨hs', hom⟩ := nf_om_iff.mp hs
    by_cases hnil : s' = .nil
    · subst hnil
      show nf (A.om (app r .nil)) = true
      refine nf_om_iff.mpr ⟨hr, ?_⟩
      have : fits r (A.om .nil) = omOK r := rfl
      rw [this] at hf
      exact hf
    · have hne : firstSm s' ≠ none := fun hc => hnil ((firstSm_none_iff s').mp hc)
      refine nf_om_iff.mpr ⟨ih r hr hs' (by rw [← fits_om hne]; exact hf), ?_⟩
      rw [omOK_app hnil]
      exact hom
  | ps s' a ih _ =>
    intro r hr hs hf
    obtain ⟨hs', hna, hd, hfp⟩ := nf_ps_iff.mp hs
    by_cases hnil : s' = .nil
    · subst hnil
      show nf (A.ps (app r .nil) a) = true
      refine nf_ps_iff.mpr ⟨hr, hna, ?_, hfp⟩
      have : fits r (A.ps .nil a) = descOK r a := rfl
      rw [this] at hf
      exact hf
    · have hne : firstSm s' ≠ none := fun hc => hnil ((firstSm_none_iff s').mp hc)
      refine nf_ps_iff.mpr ⟨ih r hr hs' (by rw [← fits_ps (a := a) hne]; exact hf), hna, ?_, hfp⟩
      rw [descOK_app hnil]
      exact hd

/-! ### §13.5 `fsP` preserves the normal form

Four claims at once, because they feed each other: the sequence member is a normal form,
its arguments stay under `a`, its first summand is a `ψ₀` whose argument is strictly under
`a`, and its whole matrix is under `ψ₀(a)`'s.  The last is what lets the `ψ₀(c)` case
recurse without a structural split lemma. -/

def FsPOK (a : A) (n : Nat) : Prop :=
  nf (fsP a n) = true
  ∧ argsLtM (mat a 0) (fsP a n) = true
  ∧ (∃ c, firstSm (fsP a n) = some (some c)
      ∧ BMS.cmpM (mat c 0) (mat a 0) = Ordering.lt)
  ∧ BMS.cmpM (mat (fsP a n) 0) (mat (.ps .nil a) 0) = Ordering.lt

theorem mat_ne_nil : ∀ (t : A) (d : Nat), t ≠ .nil → mat t d ≠ [] := by
  intro t d h
  cases t with
  | nil => exact absurd rfl h
  | om r => show mat r d ++ [[d, 1]] ≠ []; simp
  | ps r a => show mat r d ++ ([d, 0] :: mat a (d + 1)) ≠ []; simp

theorem cmpM_prefix_lt' (X Y : Matrix) (h : Y ≠ []) : BMS.cmpM X (X ++ Y) = Ordering.lt := by
  cases Y with
  | nil => exact absurd rfl h
  | cons c U => exact BMS.cmpM_prefix_lt X c U

theorem descOK_of_le {r c y : A} (h : (BMS.cmpM (mat y 0) (mat c 0) != Ordering.gt) = true)
    (hd : descOK r c = true) : descOK r y = true := by
  show (match lastSm r with
    | none => true | some none => true
    | some (some x) => BMS.cmpM (mat y 0) (mat x 0) != Ordering.gt) = true
  have hd' : (match lastSm r with
    | none => true | some none => true
    | some (some x) => BMS.cmpM (mat c 0) (mat x 0) != Ordering.gt) = true := hd
  cases hl : lastSm r with
  | none => rfl
  | some o => cases o with
    | none => rfl
    | some x =>
      rw [hl] at hd'
      exact BMS.leM_trans h hd'

/-- 場合 3 の要 — 引数 `c` が、新しい引数 `b ⊕ fsP c n` を超えないこと。 -/
def CaseThree : Prop := ∀ (b c : A), c ≠ .nil → ∀ (n : Nat),
    nf (.ps b c) = true → fpOK (.ps b c) = true → FsPOK c n →
    (BMS.cmpM (mat c 0) (mat (app b (fsP c n)) 0) != Ordering.gt) = true

/-- 不動点条件が与える不等式 — `a ∈ C₀(a)` の最後の加数ぶん。 -/
theorem fpOK_arg_lt {b c : A} (h : fpOK (A.ps b c) = true) :
    BMS.cmpM (mat c 0) (mat (A.ps b c) 0) = Ordering.lt := by
  have h' : (argsLtM (mat (A.ps b c) 0) b
      && (BMS.cmpM (mat c 0) (mat (A.ps b c) 0) == Ordering.lt)
      && argsLtM (mat (A.ps b c) 0) c) = true := h
  cases hcmp : BMS.cmpM (mat c 0) (mat (A.ps b c) 0) with
  | lt => rfl
  | eq => rw [hcmp] at h'; simp at h'
  | gt => rw [hcmp] at h'; simp at h'

/-- **場合 3 は閉じている。** 仮定は不動点条件 `fpOK (ps b c)` だけ — 標準形の残りも
    `FsPOK` も使わない。§13.7 が証明の筋を書く。 -/
theorem caseThree : CaseThree := by
  intro b c _ n _ hfp _
  have h1 : BMS.cmpM (mat c 0) (mat b 0 ++ ([0, 0] :: mat c 1)) = Ordering.lt :=
    fpOK_arg_lt hfp
  cases hCB : BMS.cmpM (mat c 0) (mat b 0) with
  | lt =>
    rw [mat_app, BMS.cmpM_lt_append _ _ _ hCB]
    rfl
  | eq =>
    rw [mat_app, BMS.cmpM_eq _ _ hCB]
    exact BMS.cmpM_self_append _ _
  | gt =>
    obtain ⟨W, hW⟩ := BMS.cmpM_gt_prefix _ _ _ hCB h1
    have h1' : BMS.cmpM W ([0, 0] :: mat c 1) = Ordering.lt := by
      rw [hW, BMS.cmpM_append_left] at h1; exact h1
    obtain ⟨Z, hZ⟩ := fsP_zero_prefix c 0
    have hZ0 : ([0, 0] :: mat c 1) = mat (fsP c 0) 0 ++ Z := hZ
    rw [hZ0] at h1'
    have hlenC : (mat c 0).length = (mat b 0).length + W.length := by
      rw [hW, List.length_append]
    have e1 : (mat c 0).length = len c := mat_len c 0
    have e2 : (mat (fsP c 0) 0).length = len (fsP c 0) := mat_len (fsP c 0) 0
    have e3 : len c ≤ len (fsP c 0) := len_fsP_zero c
    have hstep := BMS.cmpM_le_of_len h1' (by omega : W.length ≤ (mat (fsP c 0) 0).length)
    obtain ⟨Z', hZ'⟩ := mat_fsP_mono c n 0
    rw [mat_app, hW, BMS.cmpM_append_left, hZ']
    exact BMS.leM_trans hstep (BMS.cmpM_self_append _ _)

theorem fsP_case3 (b c : A) (hc : c ≠ .nil) (n : Nat)
    (hnf : nf (.ps b c) = true) (hfp : fpOK (.ps b c) = true) (IH : FsPOK c n)
    (hshape : fsP (.ps b c) n = .ps .nil (app b (fsP c n))) : FsPOK (.ps b c) n := by
  obtain ⟨hnb, hnc, hdbc, hfpc⟩ := nf_ps_iff.mp hnf
  obtain ⟨hns, hargs, ⟨c', hfs, hlt'⟩, hmat⟩ := IH
  have hLa := caseThree b c hc n hnf hfp ⟨hns, hargs, ⟨c', hfs, hlt'⟩, hmat⟩
  have hfpb : fpOK b = true := fpOK_left_ps hfp
  have hX : mat (app b (fsP c n)) 0 = mat b 0 ++ mat (fsP c n) 0 := mat_app _ _ _
  have hA : mat (A.ps b c) 0 = mat b 0 ++ mat (A.ps .nil c) 0 := rfl
  -- the new argument is strictly under the old one
  have hXA : BMS.cmpM (mat (app b (fsP c n)) 0) (mat (A.ps b c) 0) = Ordering.lt := by
    rw [hX, hA, BMS.cmpM_append_left]
    exact hmat
  -- `b` still admits what follows it
  have hfits : fits b (fsP c n) = true := by
    show (match firstSm (fsP c n) with
      | none => true | some none => omOK b | some (some y) => descOK b y) = true
    rw [hfs]
    exact descOK_of_le (by rw [hlt']; rfl) hdbc
  have hnX : nf (app b (fsP c n)) = true := nf_app _ b hnb hns hfits
  have hbX : (BMS.cmpM (mat b 0) (mat (app b (fsP c n)) 0) != Ordering.gt) = true := by
    rw [hX, cmpM_prefix_lt' _ _ (mat_ne_nil _ 0 (by
      intro hcc; rw [hcc] at hfs; exact absurd hfs (by simp [firstSm])))]
    rfl
  have hfpX : fpOK (app b (fsP c n)) = true := by
    show argsLtM (mat (app b (fsP c n)) 0) (app b (fsP c n)) = true
    rw [argsLtM_app]
    rw [argsLtM_mono hbX b hfpb, argsLtM_mono hLa _ hargs]
    rfl
  refine ⟨?_, ?_, ⟨app b (fsP c n), ?_, hXA⟩, ?_⟩
  · rw [hshape]
    exact nf_ps_iff.mpr ⟨rfl, hnX, rfl, hfpX⟩
  · rw [hshape]
    show (argsLtM (mat (A.ps b c) 0) .nil
      && (BMS.cmpM (mat (app b (fsP c n)) 0) (mat (A.ps b c) 0) == Ordering.lt)
      && argsLtM (mat (A.ps b c) 0) (app b (fsP c n))) = true
    rw [hXA, argsLtM_mono (by rw [hXA]; rfl) _ hfpX]
    rfl
  · rw [hshape]; rfl
  · rw [hshape]
    show (BMS.cmpCol [0, 0] [0, 0]).then
      (BMS.cmpM (mat (app b (fsP c n)) 1) (mat (A.ps b c) 1)) = Ordering.lt
    rw [BMS.cmpCol_refl]
    show BMS.cmpM (mat (app b (fsP c n)) 1) (mat (A.ps b c) 1) = Ordering.lt
    rw [show (1 : Nat) = 0 + 1 from rfl, cmpM_mat_depth]
    exact hXA

/-- **`fsP` は標準形を保つ。** 仮定なし — 場合 3 は `caseThree` が閉じた。 -/
theorem fsP_ok : ∀ (a : A), a ≠ .nil → nf a = true → fpOK a = true →
    ∀ (n : Nat), FsPOK a n := by
  intro a
  induction a with
  | nil => intro h; exact absurd rfl h
  | om b _ =>
    intro _ hnf _ n
    obtain ⟨j, hj⟩ := om_all b hnf
    subst hj
    have htw := towArg_ok j n
    have hlt : BMS.cmpM (mat (towArg (omPow j) n) 0) (mat (A.om (omPow j)) 0) = Ordering.lt :=
      towArg_lt_om (omPow j) n
    have hshape : fsP (A.om (omPow j)) n = .ps .nil (towArg (omPow j) n) := by
      show iterOm (omPow j) n = _
      exact iterOm_eq _ n
    refine ⟨?_, ?_, ⟨towArg (omPow j) n, ?_, hlt⟩, ?_⟩
    · rw [hshape]; exact nf_ps_iff.mpr ⟨rfl, htw.1, rfl, htw.2⟩
    · rw [hshape]
      show (argsLtM (mat (A.om (omPow j)) 0) .nil
        && (BMS.cmpM (mat (towArg (omPow j) n) 0) (mat (A.om (omPow j)) 0) == Ordering.lt)
        && argsLtM (mat (A.om (omPow j)) 0) (towArg (omPow j) n)) = true
      rw [hlt, argsLtM_mono (leM_of_lt hlt) _ htw.2]
      rfl
    · rw [hshape]; rfl
    · rw [hshape]
      show (BMS.cmpCol [0, 0] [0, 0]).then
        (BMS.cmpM (mat (towArg (omPow j) n) 1) (mat (A.om (omPow j)) 1)) = Ordering.lt
      rw [BMS.cmpCol_refl]
      show BMS.cmpM (mat (towArg (omPow j) n) 1) (mat (A.om (omPow j)) 1) = Ordering.lt
      rw [show (1 : Nat) = 0 + 1 from rfl, cmpM_mat_depth]
      exact hlt
  | ps b c _ ihc =>
    intro _ hnf hfp n
    cases c with
    | nil =>
      obtain ⟨hnb, _, _, _⟩ := nf_ps_iff.mp hnf
      have hfpb : fpOK b = true := fpOK_left_ps hfp
      have hA : mat (A.ps b .nil) 0 = mat b 0 ++ [[0, 0]] := rfl
      have hbA : BMS.cmpM (mat b 0) (mat (A.ps b .nil) 0) = Ordering.lt := by
        rw [hA]; exact BMS.cmpM_prefix_lt _ _ _
      have hshape : fsP (A.ps b .nil) n = rep b n := rfl
      refine ⟨?_, ?_, ⟨b, ?_, hbA⟩, ?_⟩
      · rw [hshape]; exact nf_rep hnb hfpb n
      · rw [hshape]
        exact argsLtM_rep (by rw [hbA]; rfl) (argsLtM_mono (leM_of_lt hbA) b hfpb) n
      · rw [hshape]; exact firstSm_rep b n
      · rw [hshape]; exact mat_rep_lt b n
    | om c' =>
      obtain ⟨_, hnc, _, hfpc⟩ := nf_ps_iff.mp hnf
      exact fsP_case3 b (.om c') (by intro hcc; exact A.noConfusion hcc) n hnf hfp
        (ihc (by intro hcc; exact A.noConfusion hcc) hnc hfpc n) rfl
    | ps c1 c2 =>
      obtain ⟨_, hnc, _, hfpc⟩ := nf_ps_iff.mp hnf
      exact fsP_case3 b (.ps c1 c2) (by intro hcc; exact A.noConfusion hcc) n hnf hfp
        (ihc (by intro hcc; exact A.noConfusion hcc) hnc hfpc n) rfl

/-! ### §13.6 `Hclosed` -/

theorem topOK_app : ∀ (s r : A), topOK r = true → topOK s = true → topOK (app r s) = true := by
  intro s
  induction s with
  | nil => intro r hr _; exact hr
  | om s' _ => intro _ _ hs; exact Bool.noConfusion hs
  | ps s' a ih _ =>
    intro r hr hs
    show topOK (app r s') = true
    exact ih r hr hs

theorem topOK_rep (b : A) : ∀ (n : Nat), topOK (rep b n) = true
  | 0 => rfl
  | k + 1 => by show topOK (rep b k) = true; exact topOK_rep b k

theorem topOK_fsP : ∀ (a : A) (n : Nat), topOK (fsP a n) = true := by
  intro a n
  cases a with
  | nil => rfl
  | om b => show topOK (iterOm b n) = true; rw [iterOm_eq]; rfl
  | ps b c => cases c with
    | nil => exact topOK_rep b n
    | om _ => rfl
    | ps _ _ => rfl

/-- **`Hclosed` の添字側。** -/
theorem nf_fs (t : A) (hnf : nf t = true) (htop : topOK t = true) (n : Nat) :
    nf (fs t n) = true ∧ topOK (fs t n) = true := by
  cases t with
  | nil => exact ⟨rfl, rfl⟩
  | om _ => exact Bool.noConfusion htop
  | ps r a =>
    obtain ⟨hnr, hna, hd, hfpa⟩ := nf_ps_iff.mp hnf
    cases a with
    | nil => exact ⟨hnr, htop⟩
    | om a' =>
      obtain ⟨hns, _, ⟨c, hfs, hlt⟩, _⟩ :=
        fsP_ok (.om a') (by intro hc; exact A.noConfusion hc) hna hfpa n
      refine ⟨nf_app _ r hnr hns ?_, topOK_app _ r htop (topOK_fsP _ n)⟩
      show (match firstSm (fsP (A.om a') n) with
        | none => true | some none => omOK r | some (some y) => descOK r y) = true
      rw [hfs]
      exact descOK_of_le (by rw [hlt]; rfl) hd
    | ps a1 a2 =>
      obtain ⟨hns, _, ⟨c, hfs, hlt⟩, _⟩ :=
        fsP_ok (.ps a1 a2) (by intro hc; exact A.noConfusion hc) hna hfpa n
      refine ⟨nf_app _ r hnr hns ?_, topOK_app _ r htop (topOK_fsP _ n)⟩
      show (match firstSm (fsP (A.ps a1 a2) n) with
        | none => true | some none => omOK r | some (some y) => descOK r y) = true
      rw [hfs]
      exact descOK_of_le (by rw [hlt]; rfl) hd

/-- **`Hclosed`。** 領域は `BMS.expand` で閉じている。 -/
theorem hclosed_supply : ∀ (S : BMS.Matrix), Reg S → ∀ (n : Nat),
    Reg (BMS.expand S n) := by
  rintro S ⟨t, hnf, htop, rfl⟩ n
  cases t with
  | nil =>
    refine ⟨.nil, rfl, rfl, ?_⟩
    show (BMS.expand? [] n).getD [] = []
    rfl
  | om _ => exact Bool.noConfusion htop
  | ps r a =>
    obtain ⟨h1, h2⟩ := nf_fs (.ps r a) hnf htop n
    refine ⟨fs (.ps r a) n, h1, h2, ?_⟩
    show (BMS.expand? (mat (A.ps r a) 0) n).getD [] = _
    rw [expand_mat (.ps r a) htop (by intro hc; exact A.noConfusion hc) n]
    rfl

/-! ### §13.7 HOW THE LAST CASE CLOSES

`CaseThree` was the only hypothesis `fsP_ok` and `hclosed_supply` carried, and it is one
inequality: when the argument's last summand is `ψ₀(c)` with `c ≠ 0`, the fundamental
sequence replaces it by `ψ₀(b ⊕ fsP c n)`, and the NEW argument must not drop below `c`.

    cmpM (mat c 0) (mat (app b (fsP c n)) 0) ≠ .gt

IT IS NOT AN ORDER FACT, IT IS A LENGTH FACT.  Both weaker statements that would have
implied it are REFUTED on the 102 instances `closureCorpus` yields, so neither half is
enough on its own —

    c ≤ fsP c n     27 of 102 fail   (it holds when `b = nil`, 0 of 42)
    c ≤ b           66 of 102 fail

— and so is the obvious repair, routing through `ψ₀` of `c` minus its last summand
(24 of the 66 fail).  What works instead: compare `c` with `b` first.  Below `b` and equal
to `b` are immediate.  ABOVE `b` is the case with content, and there the fixed-point
condition `c < b ⊕ ψ₀(c)` forces `b` to be a PREFIX of `c` (`cmpM_gt_prefix`), so the whole
inequality cancels down to its tail `W` against `fsP c n`.  Now `Evidence/Region.lean` §9
applies: `fsP c 0`'s matrix is a prefix of `ψ₀(c)`'s and is no shorter than `c`, and `W` is
a tail of `c`, so `|W| ≤ |c| ≤ |fsP c 0|` — and a matrix that is `< Y ++ Z` and no longer
than `Y` is `≤ Y` (`Evidence/CmpM.lean`'s `cmpM_le_of_len`).  Raising `n` only appends on
the right, which cannot lower the bound.

Nothing in the argument uses the descending condition, `FsPOK`, or the value — only
`a ∈ C₀(a)`.  The `#guard`s below are kept as the measurement that pointed at the shape. -/

def caseThreePairs : List (A × A) :=
  (closureCorpus.filter nf).filterMap fun t =>
    match t with
    | .ps _ (.ps b c) => if c == .nil then none else some (b, c)
    | _ => none

#guard caseThreePairs.length == 102
#guard caseThreePairs.all fun p => (List.range 4).all fun n =>
  BMS.cmpM (mat p.2 0) (mat (app p.1 (fsP p.2 n)) 0) != Ordering.gt
-- 弱い 2 つは反証される。
#guard (caseThreePairs.filter fun p => !((List.range 4).all fun n =>
  BMS.cmpM (mat p.2 0) (mat (fsP p.2 n) 0) != Ordering.gt)).length == 27
#guard (caseThreePairs.filter fun p =>
  BMS.cmpM (mat p.2 0) (mat p.1 0) == Ordering.gt).length == 66

/-- 最後の加数を落とした残り。 -/
def hdOf : A → A | .nil => .nil | .om r => r | .ps r _ => r

-- `ψ₀(hdOf c)` を経由する明らかな修理も落ちる。`c > b` の 66 件のうち 24 件で
-- 尾 `W` が `ψ₀(hdOf c)` を超える。§13.7 が長さで通す理由。
#guard (caseThreePairs.filter fun p =>
  BMS.cmpM (mat p.2 0) (mat p.1 0) == Ordering.gt
  && BMS.cmpM ((mat p.2 0).drop (mat p.1 0).length)
       (mat (A.ps .nil (hdOf p.2)) 0) == Ordering.gt).length == 24
-- 一方 `ψ₀(hdOf c) ≤ fsP c n` の側は 102 件すべてで成り立つ。
#guard caseThreePairs.all fun p => (List.range 4).all fun n =>
  BMS.cmpM (mat (A.ps .nil (hdOf p.2)) 0) (mat (fsP p.2 n) 0) != Ordering.gt

/-! ## §14 `Hlim`, REDUCED TO THE LAST SUMMAND

`fs` acts on the last summand — `fs (r ⊕ ψ₀(a)) n = r ⊕ fsP a n` — so the value of an
expansion is the value of the untouched prefix PLUS the value of the sequence member.
Saying that at all requires

    sumVal (app r s) = sumVal r ⊕ sumVal s

and THAT requires associativity of `plus`, which the repo did not have; it is now
`Evidence/CNVOps.lean` §19.  With it `Hlim` splits along the same seam as `Hclosed` did:

    ArgLim      the four clauses for ONE principal term `ω^(argVal a)` and its
                sequence `fsP a n` — the three cases of `fsP`, which is where
                `Evidence/WF.lean`'s `lim_clauses_repAdd` / `lim_clauses_phi_arg` /
                `lim_clauses_fsGen` are aimed
    PrefixLim   adding a fixed prefix on the left preserves the four clauses —
                `lim_clauses_sum` stated for a whole `plus` prefix instead of one summand

`PrefixLim` is TRUE AS STATED (no side condition): `plus` is ordinal addition on `CNV`, so
`P ⊕ x < P ⊕ y ↔ x < y`, and cofinality splits on whether `s ≤ P`.  It needs left
monotonicity and a subtraction, neither of which is in the repo yet. -/

theorem cnv_argVal (a : A) : CNV (argVal a) = true := by
  show CNV (if omN a = 0 then sumVal a else plus (epsT (omN a - 1)) (sumVal a)) = true
  by_cases h : omN a = 0
  · rw [if_pos h]; exact cnv_sumVal a
  · rw [if_neg h]; exact cnv_plus (cnv_epsT _) (cnv_sumVal a)

theorem sumVal_app : ∀ (s r : A), sumVal (app r s) = plus (sumVal r) (sumVal s) := by
  intro s
  induction s with
  | nil => intro r; rfl
  | om s' ih => intro r; exact ih r
  | ps s' a ih _ =>
    intro r
    show plus (sumVal (app r s')) (omegaNF (argVal a))
      = plus (sumVal r) (plus (sumVal s') (omegaNF (argVal a)))
    rw [ih r]
    exact plus_assoc (cnv_sumVal r) (cnv_sumVal s') (cnv_omegaNF (cnv_argVal a))

theorem sumVal_fs_lim {r a : A} (ha : a ≠ .nil) (n : Nat) :
    sumVal (fs (.ps r a) n) = plus (sumVal r) (sumVal (fsP a n)) := by
  have h : fs (.ps r a) n = app r (fsP a n) := by
    cases a with
    | nil => exact absurd rfl ha
    | om _ => rfl
    | ps _ _ => rfl
  rw [h, sumVal_app]

theorem kindA_lim {t : A} (htop : topOK t = true) (h : kindA t = BMS.Kind.lim) :
    ∃ r a, a ≠ .nil ∧ t = .ps r a := by
  cases t with
  | nil => exact BMS.Kind.noConfusion h
  | om _ => exact Bool.noConfusion htop
  | ps r a => cases a with
    | nil => exact BMS.Kind.noConfusion h
    | om a' => exact ⟨r, .om a', by intro hc; exact A.noConfusion hc, rfl⟩
    | ps a1 a2 => exact ⟨r, .ps a1 a2, by intro hc; exact A.noConfusion hc, rfl⟩

/-- 最後の加数の極限節。 -/
def ArgLim : Prop := ∀ (a : A), a ≠ .nil → nf a = true → fpOK a = true →
    LimClauses (omegaNF (argVal a)) (fun n => sumVal (fsP a n))

/-- 前置きを足しても極限節は保たれる。**側条件は無い** — `Evidence/CNVOps.lean` §23。 -/
def PrefixLim : Prop := ∀ (P V : Term) (g : Nat → Term),
    CNV P = true → CNV V = true → LimClauses V g →
    LimClauses (plus P V) (fun n => plus P (g n))

/-- **前置きの穴は閉じている。** -/
theorem prefixLim : PrefixLim :=
  fun P V g hP hV h => lim_clauses_prefix hP hV g h

/-- **`Hlim`。** 残る仮定は `ArgLim` ただ 1 つ。 -/
theorem hlim_supply (HA : ArgLim) :
    ∀ (S : BMS.Matrix) (v : Term), Reg S → Val S v → BMS.kind S = BMS.Kind.lim →
    ∃ f : Nat → Term, inT v = true
      ∧ (∀ n, Val (BMS.expand S n) (f n))
      ∧ (∀ n, inT (f n) = true)
      ∧ (∀ n, lt (f n) v = true)
      ∧ (∀ n, lt (f n) (f (n + 1)) = true)
      ∧ (∀ s, inT s = true → lt s v = true → ∃ n, le s (f n) = true) := by
  rintro S v _ ⟨t, hnf, htop, rfl, rfl⟩ hk
  rw [kind_mat t htop] at hk
  obtain ⟨r, a, ha, rfl⟩ := kindA_lim htop hk
  obtain ⟨_, hna, _, hfpa⟩ := nf_ps_iff.mp hnf
  have hlc : LimClauses (sumVal (A.ps r a)) (fun n => sumVal (fs (A.ps r a) n)) := by
    have h := prefixLim (sumVal r) (omegaNF (argVal a)) (fun n => sumVal (fsP a n))
      (cnv_sumVal r) (cnv_omegaNF (cnv_argVal a)) (HA a ha hna hfpa)
    have hf : (fun n => sumVal (fs (A.ps r a) n))
        = (fun n => plus (sumVal r) (sumVal (fsP a n))) :=
      funext (fun n => sumVal_fs_lim ha n)
    show LimClauses (plus (sumVal r) (omegaNF (argVal a))) _
    rw [hf]
    exact h
  obtain ⟨_, h2, h3, h4⟩ := hlc
  refine ⟨fun n => sumVal (fs (A.ps r a) n), inT_sumVal _, ?_,
    fun n => inT_sumVal _, h2, h3, h4⟩
  intro n
  obtain ⟨g1, g2⟩ := nf_fs (.ps r a) hnf htop n
  refine ⟨fs (A.ps r a) n, g1, g2, ?_, rfl⟩
  show (BMS.expand? (mat (A.ps r a) 0) n).getD [] = mat (fs (A.ps r a) n) 0
  rw [expand_mat (.ps r a) htop (by intro hc; exact A.noConfusion hc) n]
  rfl

/-! ## §15 `ArgLim` IS A RECURSION, AND ITS THREE BASE CASES

MEASURED FIRST (Cert.lean §22's discipline).  Over the 80 normal-form ARGUMENTS the closure
corpus yields, `omegaNF (argVal a)` has THREE shapes, not one:

    74   `φ̄(0, argVal a)`      the ordinary case
     2   `argVal a` itself     `argVal a` is already a fixed point of `ω^·`
     4   re-counted            `argVal a = γ ⊕ m` with `γ` a fixed point, so
                               `omegaNF` steps down to `φ̄(0, γ ⊕ (m-1))`

— which is why the target of `ArgLim` cannot be written as one `phi` and why the three
cases of `fsP` have to be taken separately.  The split is 2 / 9 / 69 over `Ω` / `ψ₀(0)` /
`ψ₀(c)` with `c ≠ 0`.

WHAT IS NOT SEPARATE IS THE THIRD CASE.  `fsP (b ⊕ ψ₀(c)) n = ψ₀(b ⊕ fsP c n)`, and

    argVal (b ⊕ ψ₀(c))   = argVal b ⊕ ω^(argVal c)
    argVal (b ⊕ fsP c n) = argVal b ⊕ sumVal (fsP c n)

so the ARGUMENT's four clauses are the inner `ArgLim`'s four clauses with a fixed prefix on
the left — `Evidence/CNVOps.lean` §23.  `argLim` below is that recursion; what is left is
three BASE facts, one per case of `fsP`, and `Evidence/WF.lean` has one combinator aimed at
each: `lim_clauses_repAdd` (A) for `ψ₀(0)`, `lim_clauses_fsGen` (B) for `Ω`,
`lim_clauses_phi_arg` (C) for the lift. -/

theorem omN_app : ∀ (s r : A), omN (app r s) = omN r + omN s := by
  intro s
  induction s with
  | nil => intro r; show omN r = omN r + 0; omega
  | om s' ih => intro r; show omN (app r s') + 1 = omN r + (omN s' + 1); rw [ih r]; omega
  | ps s' a ih _ => intro r; show omN (app r s') = omN r + omN s'; exact ih r

theorem omN_rep (b : A) : ∀ (n : Nat), omN (rep b n) = 0
  | 0 => rfl
  | k + 1 => by show omN (rep b k) = 0; exact omN_rep b k

theorem omN_fsP : ∀ (c : A) (n : Nat), c ≠ .nil → omN (fsP c n) = 0 := by
  intro c n h
  cases c with
  | nil => exact absurd rfl h
  | om b => show omN (iterOm b n) = 0; rw [iterOm_eq]; rfl
  | ps b d => cases d with
    | nil => exact omN_rep b n
    | om _ => rfl
    | ps _ _ => rfl

/-- **引数の値は前置きと最後の加数に分かれる。** `Ω` の段の読み替えも前置きに入る。 -/
theorem argVal_ps (b c : A) : argVal (.ps b c) = plus (argVal b) (omegaNF (argVal c)) := by
  show (if omN b = 0 then sumVal (A.ps b c)
        else plus (epsT (omN b - 1)) (sumVal (A.ps b c)))
      = plus (argVal b) (omegaNF (argVal c))
  by_cases h : omN b = 0
  · rw [if_pos h]
    show plus (sumVal b) (omegaNF (argVal c)) = plus (argVal b) (omegaNF (argVal c))
    show plus (sumVal b) (omegaNF (argVal c))
      = plus (if omN b = 0 then sumVal b else plus (epsT (omN b - 1)) (sumVal b))
          (omegaNF (argVal c))
    rw [if_pos h]
  · rw [if_neg h]
    show plus (epsT (omN b - 1)) (plus (sumVal b) (omegaNF (argVal c)))
      = plus (if omN b = 0 then sumVal b else plus (epsT (omN b - 1)) (sumVal b))
          (omegaNF (argVal c))
    rw [if_neg h]
    exact (plus_assoc (cnv_epsT _) (cnv_sumVal b) (cnv_omegaNF (cnv_argVal c))).symm

/-- 同じ分解を `app` の側で。`s` は `Ω` を含まない (`fsP` の像はそう)。 -/
theorem argVal_app {s : A} (hs : omN s = 0) (b : A) :
    argVal (app b s) = plus (argVal b) (sumVal s) := by
  show (if omN (app b s) = 0 then sumVal (app b s)
        else plus (epsT (omN (app b s) - 1)) (sumVal (app b s)))
      = plus (argVal b) (sumVal s)
  rw [omN_app s b, hs, Nat.add_zero, sumVal_app]
  by_cases h : omN b = 0
  · rw [if_pos h]
    show plus (sumVal b) (sumVal s)
      = plus (if omN b = 0 then sumVal b else plus (epsT (omN b - 1)) (sumVal b)) (sumVal s)
    rw [if_pos h]
  · rw [if_neg h]
    show plus (epsT (omN b - 1)) (plus (sumVal b) (sumVal s))
      = plus (if omN b = 0 then sumVal b else plus (epsT (omN b - 1)) (sumVal b)) (sumVal s)
    rw [if_neg h]
    exact (plus_assoc (cnv_epsT _) (cnv_sumVal b) (cnv_sumVal s)).symm

/-! ### §15.1 The three cases, as named holes -/

/-- 場合 2 — 最後の加数が `ψ₀(0)`。列は `ψ₀(b)` の反復。 -/
def ArgLimRep : Prop := ∀ (b : A), nf (.ps b .nil) = true → fpOK (.ps b .nil) = true →
    LimClauses (omegaNF (argVal (.ps b .nil))) (fun n => sumVal (fsP (.ps b .nil) n))

/-- 場合 1 — 最後の加数が `Ω`。列は `Ω` の塔。 -/
def ArgLimOm : Prop := ∀ (b : A), nf (.om b) = true → fpOK (.om b) = true →
    LimClauses (omegaNF (argVal (.om b))) (fun n => sumVal (fsP (.om b) n))

/-- 場合 3 — 引数の列を `ω^·` で持ち上げる段だけ。 -/
def ArgLimLift : Prop := ∀ (b c : A), c ≠ .nil → nf (.ps b c) = true → fpOK (.ps b c) = true →
    LimClauses (argVal (.ps b c)) (fun n => argVal (app b (fsP c n))) →
    LimClauses (omegaNF (argVal (.ps b c))) (fun n => sumVal (fsP (.ps b c) n))

/-- **`ArgLim` は再帰である。** 場合 3 の引数側の 4 連言は、内側の `ArgLim` に
    `Evidence/CNVOps.lean` §23 の前置き組み合わせ子を当てて出る。 -/
theorem argLim (H1 : ArgLimRep) (H2 : ArgLimOm) (H3 : ArgLimLift) : ArgLim := by
  intro a
  induction a with
  | nil => intro h; exact absurd rfl h
  | om b _ => intro _ hnf hfp; exact H2 b hnf hfp
  | ps b c _ ihc =>
    intro _ hnf hfp
    cases c with
    | nil => exact H1 b hnf hfp
    | om c' =>
      obtain ⟨_, hnc, _, hfpc⟩ := nf_ps_iff.mp hnf
      refine H3 b (.om c') (by intro h; exact A.noConfusion h) hnf hfp ?_
      have hIH := ihc (by intro h; exact A.noConfusion h) hnc hfpc
      have hpre := lim_clauses_prefix (P := argVal b) (V := omegaNF (argVal (.om c')))
        (cnv_argVal b) (cnv_omegaNF (cnv_argVal (.om c'))) _ hIH
      rw [← argVal_ps b (.om c')] at hpre
      have hfun : (fun n => plus (argVal b) (sumVal (fsP (A.om c') n)))
          = (fun n => argVal (app b (fsP (A.om c') n))) :=
        funext fun n => (argVal_app (omN_fsP (.om c') n (by intro h; exact A.noConfusion h)) b).symm
      rw [hfun] at hpre
      exact hpre
    | ps c1 c2 =>
      obtain ⟨_, hnc, _, hfpc⟩ := nf_ps_iff.mp hnf
      refine H3 b (.ps c1 c2) (by intro h; exact A.noConfusion h) hnf hfp ?_
      have hIH := ihc (by intro h; exact A.noConfusion h) hnc hfpc
      have hpre := lim_clauses_prefix (P := argVal b) (V := omegaNF (argVal (.ps c1 c2)))
        (cnv_argVal b) (cnv_omegaNF (cnv_argVal (.ps c1 c2))) _ hIH
      rw [← argVal_ps b (.ps c1 c2)] at hpre
      have hfun : (fun n => plus (argVal b) (sumVal (fsP (A.ps c1 c2) n)))
          = (fun n => argVal (app b (fsP (A.ps c1 c2) n))) :=
        funext fun n =>
          (argVal_app (omN_fsP (.ps c1 c2) n (by intro h; exact A.noConfusion h)) b).symm
      rw [hfun] at hpre
      exact hpre

/-! ### §15.2 THE MEASUREMENT

The population is every normal-form argument the closure corpus contains. -/

def argCorpus : List A :=
  (closureCorpus.filterMap fun t =>
    match t with
    | .ps _ a => if a == .nil then none else some a
    | _ => none).eraseDups.filter (fun a => nf a && fpOK a)

#guard argCorpus.length == 80
-- `omegaNF (argVal a)` は 1 つの形ではない。
#guard (argCorpus.filter fun a => omegaNF (argVal a) == phi zero (argVal a)).length == 74
#guard (argCorpus.filter fun a => omegaNF (argVal a) == argVal a).length == 2
#guard (argCorpus.filter fun a => omegaNF (argVal a) != phi zero (argVal a)
  && omegaNF (argVal a) != argVal a).length == 4
-- 3 場合の内訳。
#guard (argCorpus.filter fun a => match a with | .om _ => true | _ => false).length == 2
#guard (argCorpus.filter fun a => match a with | .ps _ .nil => true | _ => false).length == 9
#guard (argCorpus.filter fun a => match a with
  | .ps _ .nil => false | .ps _ _ => true | _ => false).length == 69
-- 場合 2 の列は `ψ₀(b)` の反復 — 組み合わせ子 (A) の形。
#guard argCorpus.all fun a => match a with
  | .ps b .nil => (List.range 4).all fun n =>
      sumVal (fsP a n) == Evidence.WF.repAdd (omegaNF (argVal b)) n
  | _ => true
-- 場合 3 の列は引数の列を `ω^·` で持ち上げたもの — 組み合わせ子 (C) の形。
#guard argCorpus.all fun a => match a with
  | .ps _ .nil => true
  | .ps b c => (List.range 4).all fun n =>
      sumVal (fsP a n) == omegaNF (argVal (app b (fsP c n)))
  | _ => true

/-! ### §15.3 THE SHAPES ARE PER CASE, AND THE OBSTACLE IS THE ORDER BRIDGE

The three shapes of `omegaNF (argVal a)` line up with the three cases of `fsP` — the
`Ω` case is ALWAYS a fixed point, the lift case is ALWAYS ordinary, and only `ψ₀(0)` mixes:

    Ω        2 / 2    `omegaNF (argVal a) = argVal a`
    ψ₀(c)   69 / 69   `omegaNF (argVal a) = φ̄(0, argVal a)`
    ψ₀(0)    5 + 4    ordinary / re-counted

So `ArgLimLift` can use ONE target shape, and `Evidence/CNVOps.lean` §24's
`lim_clauses_phi_arg_nf'` is the combinator for it — the un-shifted core (C), which is what
a certificate needs.  What it still costs is the SHAPE FACT, and that is where the matrix
order has to be cashed into the value order:

    in 39 of the 69 the prefix `argVal b` contributes nothing, so the target IS
    `ω^(argVal c)` — and in 0 of those 39 is that a fixed point
    of the 3 whose last summand's argument is an `Ω` level, `argVal b` is zero in 0

`fpOK` is what buys both (an `Ω` inside the argument forces a big enough prefix), and
turning `fpOK`'s MATRIX inequality into that VALUE fact is the next step.  §9.1 is the
standing warning about which direction is safe. -/

#guard (argCorpus.filter fun a => match a with | .om _ => true | _ => false).all
  (fun a => omegaNF (argVal a) == argVal a)
#guard (argCorpus.filter fun a => match a with
  | .ps _ .nil => false | .ps _ _ => true | _ => false).all
  (fun a => omegaNF (argVal a) == phi zero (argVal a))
#guard ((argCorpus.filter fun a => match a with | .ps _ .nil => true | _ => false).filter
  (fun a => omegaNF (argVal a) == phi zero (argVal a))).length == 5
-- 前置きが消える 39 件のうち、目標が不動点になるものは無い。
#guard (argCorpus.filter fun a => match a with
  | .ps _ .nil => false
  | .ps b c => argVal (A.ps b c) == omegaNF (argVal c)
  | _ => false).length == 39
#guard (argCorpus.filter fun a => match a with
  | .ps _ .nil => false
  | .ps b c => (argVal (A.ps b c) == omegaNF (argVal c)) && (omegaNF (argVal c) == argVal c)
  | _ => false).length == 0
-- 最後の加数の引数が `Ω` の段なら、前置きは消えない。
#guard (argCorpus.filter fun a => match a with | .ps _ (.om _) => true | _ => false).length == 3
#guard (argCorpus.filter fun a => match a with
  | .ps b (.om _) => argVal b == zero | _ => false).length == 0

/-! ### §15.4 THE LIFT CASE IS `ω^·` PRESERVING THE LIMIT CLAUSES — AND NOT `φ̄(0,·)`

CORRECTION TO THE OBVIOUS READING.  §15.3 measures the lift case's TARGET as `φ̄(0, argVal a)`
in all 69, which suggests §24's un-shifted core (C) closes it.  It does not: the SEQUENCE is
`omegaNF (argVal (b ⊕ fsP c n))`, and in **2 of the 69** some member of that sequence is one
`omegaNF` RE-COUNTS, so it is not `φ̄(0, ·)` of anything the combinator is given.  `φ̄(0,y)` and
`ω^y` are different ordinals exactly when `y` has trailing `1`s after a fixed point, so the
`φ̄` combinator proves clauses about a DIFFERENT sequence.

What the case actually is, with no shape hypothesis at all: `ω^·` preserves the four
clauses.  `sumVal (fsP (b ⊕ ψ₀(c)) n) = ω^(argVal (b ⊕ fsP c n))` — the `ψ₀` in front of the
sequence member IS the `ω^·` — so `ArgLimLift` and `OmegaLim` are the same statement. -/

theorem sumVal_fsP_lift {b c : A} (hc : c ≠ .nil) (n : Nat) :
    sumVal (fsP (.ps b c) n) = omegaNF (argVal (app b (fsP c n))) := by
  rw [fsP_ps_ne b c n hc]
  show plus (sumVal A.nil) (omegaNF (argVal (app b (fsP c n)))) = _
  exact plus_zero_left (isAP_omegaNF _)

/-- `ω^·` は極限節を保つ。 -/
def OmegaLim : Prop := ∀ (X : Term) (g : Nat → Term), CNV X = true →
    LimClauses X g → LimClauses (omegaNF X) (fun n => omegaNF (g n))

/-- **場合 3 は `OmegaLim` そのもの。** -/
theorem argLimLift_of (H : OmegaLim) : ArgLimLift := by
  intro b c hc _ _ hg
  have h := H (argVal (.ps b c)) (fun n => argVal (app b (fsP c n))) (cnv_argVal _) hg
  have hfun : (fun n => omegaNF (argVal (app b (fsP c n))))
      = (fun n => sumVal (fsP (A.ps b c) n)) :=
    funext fun n => (sumVal_fsP_lift hc n).symm
  rw [hfun] at h
  exact h

-- 目標は 69/69 で `φ̄(0, ·)` だが、列の側は違う: 2 件で `omegaNF` が数え直す。
#guard (argCorpus.filter fun a => match a with
  | .ps _ .nil => false
  | .ps b c => (List.range 5).any fun n =>
      omegaNF (argVal (app b (fsP c n))) != phi zero (argVal (app b (fsP c n)))
  | _ => false).length == 2

/-! ### §15.5 `OmegaLim` SPLITS

Clauses 1–3 are `cnv_omegaNF` and `Evidence/CNVOps.lean` §27's `omegaNF_mono`, and §28 leaves
`omegaNF_mono` owing one fact — D3, that `dnArg` cannot collapse two different arguments.  So
the 69/80 case is now exactly

    OmegaCof   cofinality: `s < ω^X → ∃ n, s ≤ ω^(g n)`

and that is all — §29 closed `DnFacts`, so `omegaNF_mono` carries no hypothesis. -/

/-- `ω^·` の共終性 — `OmegaLim` の第 4 連言だけ。 -/
def OmegaCof : Prop := ∀ (X : Term) (g : Nat → Term), CNV X = true → LimClauses X g →
    ∀ s, inT s = true → lt s (omegaNF X) = true → ∃ n, le s (omegaNF (g n)) = true

/-- **`OmegaLim` に残るのは共終性だけ。** 連言 1〜3 は `CNVOps` §26–§29。 -/
theorem omegaLim_of (C : OmegaCof) : OmegaLim := by
  intro X g hX hlc
  obtain ⟨h1, h2, h3, h4⟩ := hlc
  exact ⟨fun n => cnv_omegaNF (h1 n),
    fun n => omegaNF_mono Evidence.WF.dnFacts (h1 n) hX (h2 n),
    fun n => omegaNF_mono Evidence.WF.dnFacts (h1 n) (h1 (n + 1)) (h3 n),
    C X g hX ⟨h1, h2, h3, h4⟩⟩

/-! ### §15.6 COFINALITY COMES DOWN TO ONE ADDITIVELY PRINCIPAL TERM

A general `s < ω^X` is covered by repeating its own HEAD: `le_repAdd_of_head` gives
`s ≤ hdOf s · (k+1)`, and `Evidence/WF.lean`'s `lt_repAdd_phi` says a repetition is below an
additively principal term exactly when ONE copy is.  Both `hdOf s` and `ω^(g n)` are
additively principal (`isAP_omegaNF`), so the whole clause collapses to the head:

    OmegaCofAP   `u` additively principal, `u < ω^X`  →  `∃ n, u < ω^(g n)`

Nothing about sums survives the reduction, which is why this is the shape to attack. -/

/-- 加法主要な項の側の共終性 — `OmegaCof` の中身。 -/
def OmegaCofAP : Prop := ∀ (X : Term) (g : Nat → Term), CNV X = true → LimClauses X g →
    ∀ u, CNV u = true → u.isAP = true → lt u (omegaNF X) = true →
      ∃ n, lt u (omegaNF (g n)) = true

/-- **共終性は加法主要な項 1 個の話に落ちる。** 一般の `s` はその頭を `repAdd` で
    覆えばよく、`lt_repAdd_phi` が「頭が下なら反復も下」を与える。 -/
theorem omegaCof_of (H : OmegaCofAP) : OmegaCof := by
  intro X g hX hlc s hin hlt
  have hcnX : CNV (omegaNF X) = true := cnv_omegaNF hX
  have hcs : CNV s = true := Evidence.WF.cnv_of_lt_cnv hin hcnX hlt
  obtain ⟨h1, h2, h3, h4⟩ := hlc
  by_cases hsz : s = zero
  · exact ⟨0, by rw [hsz]; exact Evidence.WF.le_zero_left (omegaNF_ne_zero (g 0))⟩
  · have hcu : CNV (Evidence.WF.hdOf s) = true := Evidence.WF.cnv_hdOf hcs
    have hapu : (Evidence.WF.hdOf s).isAP = true := isAP_hdOf hcs hsz
    have hus : le (Evidence.WF.hdOf s) s = true := Evidence.WF.le_hdOf_self s hcs
    have hux : lt (Evidence.WF.hdOf s) (omegaNF X) = true :=
      Evidence.WF.lt_of_le_of_lt (Evidence.WF.frag_of_cnv _ hcu) (Evidence.WF.frag_of_cnv _ hcs)
        (Evidence.WF.frag_of_cnv _ hcnX) hus hlt
    obtain ⟨n, hn⟩ := H X g hX ⟨h1, h2, h3, h4⟩ (Evidence.WF.hdOf s) hcu hapu hux
    refine ⟨n, ?_⟩
    obtain ⟨k, hk⟩ := Evidence.WF.le_repAdd_of_head hcu hapu s hcs (Evidence.WF.le_self _)
    obtain ⟨p, q, hpq⟩ := Evidence.WF.eq_phi_of_isAP_cnv hcu hapu
    obtain ⟨c, d, hcd⟩ :=
      Evidence.WF.eq_phi_of_isAP_cnv (cnv_omegaNF (h1 n)) (isAP_omegaNF (g n))
    have hcrep : CNV (Evidence.WF.repAdd (Evidence.WF.hdOf s) k) = true := by
      rw [hpq]; exact Evidence.WF.cnv_repAdd (by rw [← hpq]; exact hcu) k
    have hrep : lt (Evidence.WF.repAdd (Evidence.WF.hdOf s) k) (omegaNF (g n)) = true := by
      rw [hpq, hcd, Evidence.WF.lt_repAdd_phi, ← hpq, ← hcd]
      exact hn
    exact Evidence.WF.le_of_lt (Evidence.WF.lt_of_le_of_lt (Evidence.WF.frag_of_cnv _ hcs)
      (Evidence.WF.frag_of_cnv _ hcrep) (Evidence.WF.frag_of_cnv _ (cnv_omegaNF (h1 n))) hk hrep)

/-! ### §15.7 THE LIFT CASE IS CLOSED

`u` additively principal and `u < ω^X`.  Two shapes, and §26's equation decides which:

    u = φ̄(a,b), a ≠ 0    `u` is its own `ω`-power, so `u < ω^X` reflects to `u < X` directly
    u = φ̄(0,b)           take `succT b`.  `ω^b ≤ u < ω^X` reflects to `b < X`; `X` is a limit
                         so `succT b < X`; and `ω^(succT b) ≥ φ̄(0,b) = u` because D2 says
                         `dnArg` drops by at most one

Either way cofinality of `g` puts the witness under some `g n`, and one more step of `g`
makes the inequality STRICT.  So `OmegaCofAP` — and with §15.5 and §15.6 above it, `OmegaLim`
and `ArgLimLift`, the 69/80 case — are theorems. -/

section
open Evidence.WF

/-- **加法主要な項の共終性。** -/
theorem omegaCofAP : OmegaCofAP := by
  intro X g hX hlc u hu hapu hlt
  obtain ⟨h1, h2, h3, h4⟩ := hlc
  obtain ⟨a, b, rfl⟩ := eq_phi_of_isAP_cnv hu hapu
  obtain ⟨hca, hcb⟩ := cnv_phi hu
  by_cases haz : a = zero
  · subst haz
    have hbX : lt b X = true := by
      refine omegaNF_lt_reflect hcb hX ?_
      exact lt_of_le_of_lt (frag_of_cnv _ (cnv_omegaNF hcb)) (frag_of_cnv _ hu)
        (frag_of_cnv _ (cnv_omegaNF hX)) (omegaNF_le_phi_zero hcb) hlt
    have hsc : CNV (succT b) = true := cnv_succT _ hcb
    have hsX : lt (succT b) X = true :=
      limClauses_succ_lt hX ⟨h1, h2, h3, h4⟩ hcb hbX
    obtain ⟨n, hn⟩ := h4 (succT b) (inT_of_cnv _ hsc) hsX
    refine ⟨n + 1, ?_⟩
    have hu' : le (phi zero b) (omegaNF (succT b)) = true := by
      rw [omegaNF_eq hsc, if_neg (by rw [isFixP_succT]; intro hc; exact Bool.noConfusion hc)]
      have hd := dnArg_ge hcb hsc (lt_succT b hcb)
      by_cases he : b = dnArg (succT b)
      · rw [← he]; exact le_self _
      · exact le_of_lt (lt_phi_arg (lt_of_le_of_ne hd he))
    have hm : le (omegaNF (succT b)) (omegaNF (g n)) = true := by
      by_cases he : succT b = g n
      · rw [he]; exact le_self _
      · exact le_of_lt (omegaNF_mono dnFacts hsc (h1 n) (lt_of_le_of_ne hn he))
    have hch : le (phi zero b) (omegaNF (g n)) = true :=
      le_trans (frag_of_cnv _ hu) (frag_of_cnv _ (cnv_omegaNF hsc))
        (frag_of_cnv _ (cnv_omegaNF (h1 n))) hu' hm
    exact lt_of_le_of_lt (frag_of_cnv _ hu) (frag_of_cnv _ (cnv_omegaNF (h1 n)))
      (frag_of_cnv _ (cnv_omegaNF (h1 (n + 1)))) hch
      (omegaNF_mono dnFacts (h1 n) (h1 (n + 1)) (h3 n))
  · have hfu : isFixP (phi a b) = true := lt_zero_left haz
    have h5 : omegaNF (phi a b) = phi a b := by rw [omegaNF_eq hu, if_pos hfu]
    have huX : lt (phi a b) X = true :=
      omegaNF_lt_reflect hu hX (by rw [h5]; exact hlt)
    obtain ⟨n, hn⟩ := h4 (phi a b) (inT_of_cnv _ hu) huX
    refine ⟨n + 1, ?_⟩
    have hm : le (phi a b) (omegaNF (g n)) = true := by
      by_cases he : phi a b = g n
      · rw [← h5, he]; exact le_self _
      · rw [← h5]
        exact le_of_lt (omegaNF_mono dnFacts hu (h1 n) (lt_of_le_of_ne hn he))
    exact lt_of_le_of_lt (frag_of_cnv _ hu) (frag_of_cnv _ (cnv_omegaNF (h1 n)))
      (frag_of_cnv _ (cnv_omegaNF (h1 (n + 1)))) hm
      (omegaNF_mono dnFacts (h1 n) (h1 (n + 1)) (h3 n))

end

/-- **`OmegaLim` は定理。** -/
theorem omegaLim : OmegaLim := omegaLim_of (omegaCof_of omegaCofAP)

/-- **場合 3 (69/80) は閉じた。** -/
theorem argLimLift_thm : ArgLimLift := argLimLift_of omegaLim

/-- **`ArgLim` に残るのは土台 2 つ。** -/
theorem argLim' (H1 : ArgLimRep) (H2 : ArgLimOm) : ArgLim := argLim H1 H2 argLimLift_thm

/-! ### §15.8 THE `ψ₀(0)` CASE IS CLOSED

`argVal (b ⊕ ψ₀(0)) = succT (argVal b)` — the last summand contributes exactly `ω^0 = 1` —
and `sumVal (rep b n) = ω^(argVal b)·(n+1)`, because `plus` drops nothing when every
component of the left argument is the right one's head (§33).  So the case is combinator (A)
at `ω^(β+1)` with step `ω^β`, and §32 supplies its bound. -/

section
open Evidence.WF

theorem sumVal_rep (b : A) : ∀ n, sumVal (rep b n) = repAdd (omegaNF (argVal b)) n
  | 0 => by
    show plus (sumVal A.nil) (omegaNF (argVal b)) = _
    exact plus_zero_left (isAP_omegaNF _)
  | k + 1 => by
    show plus (sumVal (rep b k)) (omegaNF (argVal b)) = _
    rw [sumVal_rep b k]
    exact plus_repAdd_self (cnv_omegaNF (cnv_argVal b)) (isAP_omegaNF _) k

/-- **場合 2 (9/80) は閉じた。** 組み合わせ子 (A)。 -/
theorem argLimRep : ArgLimRep := by
  intro b _ _
  have hcb : CNV (argVal b) = true := cnv_argVal b
  have hsb : CNV (succT (argVal b)) = true := cnv_succT _ hcb
  have hav : argVal (A.ps b .nil) = succT (argVal b) := by
    rw [argVal_ps]
    show plus (argVal b) (omegaNF zero) = _
    rw [omegaNF_zero]
    exact plus_one_eq_succT _ hcb
  have hseq : (fun n => sumVal (fsP (A.ps b .nil) n))
      = (fun n => repAdd (omegaNF (argVal b)) n) :=
    funext fun n => sumVal_rep b n
  obtain ⟨p, q, hpq⟩ := eq_phi_of_isAP_cnv (cnv_omegaNF hcb) (isAP_omegaNF _)
  obtain ⟨c, d, hcd⟩ := eq_phi_of_isAP_cnv (cnv_omegaNF hsb) (isAP_omegaNF _)
  have key := lim_clauses_repAdd (c := c) (d := d) (p := p) (q := q)
    (by rw [← hpq]; exact cnv_omegaNF hcb)
    (by rw [← hpq, ← hcd]
        exact omegaNF_mono dnFacts hcb hsb (lt_succT _ hcb))
    (by rw [← hcd]; exact cnv_omegaNF hsb)
    (by rw [← hpq, ← hcd]
        exact fun x hx hax hlx => ap_le_omegaNF_of_lt_succT hcb hx hax hlx)
  show LimClauses (omegaNF (argVal (A.ps b .nil))) (fun n => sumVal (fsP (A.ps b .nil) n))
  rw [hav, hseq, hcd, hpq]
  exact key

end

end Evidence.Region
