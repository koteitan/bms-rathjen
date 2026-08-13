/-
Trans/DictInv.lean — Rathjen 𝔗(M) → Buchholz OT_B, the inverse of `dict` (2026-08-13)

WHAT IT IS.  `dictInv : Term → Option BT` maps a term of Rathjen's 𝔗(M) to the standard
Buchholz term denoting the same ordinal, or `none` where no Buchholz term does.  It is a
translation in the direction nothing else in this repository goes: `oR = (1+·) ∘ dict ∘
oRB` runs BMS → Buchholz → 𝔗(M), and this is the return leg of the second stage.

WHY IT IS ALSO THE FIRST HONEST CHECK ON `dict`.  `Trans/Dict.lean` calls itself
"candidate / 予想 tier"; its order-preservation is measurement, not theorem.  Every gate
in `Evidence/SqV.lean` compares two things built from each other — GATE 1 is a round trip
through `oR`, GATES 2 and 3 match `sqv` against the table — so none of them can see an
error in `dict`.  A round trip through an inverse needs no external reference implementation, and it now
reaches every row of the table, `(0,0)(1,1)(2,2)` included.

HOW IT WAS DERIVED — read off `wcnf`/`collapse`, not guessed:

    wcnf w splits each AP component p of the argument as p = ω^g with g = w·a + r,
    and reports the pair (a, c) with c = ω^r; that is p = w^a·c.
    collapse u folds the pairs left to right from base = 0 (u = 0) or reg u + 1 (u ≥ 1),
    Veblen range (a < w):  acc := φ(a, base + (c⊖1)),  then  acc := φ(a, acc + c)
    strongly critical (a ≥ w):  acc := ψ_{Z u}(i),  i := (Δ₁⊖1) + Δ₂ + …
    and returns ω^(reg u + acc + ρ) with ρ the base-w tail.

So the inverse is three readings, each of which was got wrong first and fixed by a
measurement, in this order:

  * WHICH LEVEL.  An AP term above Ω is ω^(Z u + y) for SOME u, not always u = 0, and
    the Veblen branch runs at every level too.  `levelOf` reads u off the term.  Fixing
    `u = 0` left `φ̄(1,Ω) = ψ₁(Ω₂)` — the smallest ε-number strictly between Z 0 and Z 1
    that is not of the form ω^(Z 0 + y) — with no preimage at all, and with it the twelve
    table rows indexed by `Ω₂ + …`.
  * WHICH ARGUMENT.  The second argument of φ̄ is not `b` but the SEMANTIC argument β°
    of [R91] 2.7, because φ̄ re-counts fixed points.  Without it every row of the shape
    `φ̄(1,ζ₀) = ε_{ζ₀+1}` fails — the same trap as §K3.20 of `Evidence/SqV.lean` and as
    `TM/FS.lean`'s provenance check.
  * HOW MANY PAIRS.  `collapse` folds; the inverse must peel.  Reading the whole of β°
    as one coefficient gives the right VALUE (`dict` is not injective) but a Buchholz
    term that is not standard — `ε_{ζ₀+1}` comes out as ψ₀(Ω·(ζ₀+1)) instead of
    ψ₀(Ω²+Ω), and `ω^(ε₀+1)` as ψ₀(ε₀+1) instead of ψ₀(Ω+1), both of which fail
    Buchholz's `G₀ < a`.  Fourteen table rows were of that kind.  The `isStd` guard at
    the bottom is what pins this, and peeling also turned the BT-side left inverse from
    328/336 into 336/336 exact.

WHERE IT SAYS `none`, and why that is right rather than a gap.  `dict` is not onto 𝔗(M).
The rejected shapes are φ̄(A,·) with A ∈ SC: φ̄(A,0) denotes A itself ([R91] 2.6(vi) last
line, which `phiNFdefault` folds away), and φ̄(A,B) for A ≥ Ω needs an argument ≥ reg u + 1
that the term does not carry.  Both are rejected structurally — by the shape, not by
trying `dict` and comparing — so the round-trip guards stay non-circular.

HOW HIGH IT GOES.  `BT` writes `D u` for every natural `u` and has no `Ω_ω`, so the whole
of it is what Buchholz's OT_B reaches below ψ₀(Ω_ω), the Takeuti-Feferman-Buchholz ordinal;
`dictInv` covers that with no level cap of its own, `Z` indices being numerals.  Above the
numerals — `Z ω`, which `dict` cannot produce — it answers `none`.  There is no silent
ceiling in between: a constant search bound of 8 used to translate `ψ₉(Ω₁₀) = φ̄(1,Z8)` to
`φ̄(1,Z7)`, a wrong answer rather than a `none`, and `levelOf` now takes its bound from the
term and refuses at it.

MEASURED (see the acceptance section at the bottom; the controls are next to the counts):
    generated CNV corpus, 750 terms   dict ∘ dictInv = id on 750, none on 0
    corpus above Ω, 89 terms          50 round trip, 39 none, 0 wrong
    table rows, 60                    60 round trip, 0 none, 0 wrong, 55 standard
    BT pool, 336 standard terms       dictInv ∘ dict = id on all 336, term for term
-/
import Trans.Dict
import Rows.TM

namespace Trans
namespace Dict

open TM (Term)
open TM.Term


/-- The index of `Z d` / `ψ_{Z d}` as a numeral, when it is one. -/
def natOfT (t : Term) : Option Nat :=
  if t == zero then some 0
  else if (toList t).all (· == TM.Term.one) then some (toList t).length else none

/-- 項が住む階層。`collapse u` の値は `reg u ≤ · < reg (u+1)` に落ちるので、
    `Z k ≤ t` を満たす最大の k で u = k+1、`t < Ω` なら u = 0。

    **探索の上限は項から取り、天井に当たったら拒否する。** 上限を定数 8 に固定していた版は、
    `ψ₉(Ω₁₀) = φ̄(1,Z8)` を `φ̄(1,Z7)` に訳した — `none` ではなく誤答である。`deg` は
    Z の添字が数字である限り十分大きく、数字でない添字 (`Z ω` など、`dict` が作れない項)
    では天井に当たって `none` になる。どちらの側にも黙った打ち切りが無い。 -/
def levelOf (t : Term) : Option Nat :=
  let n := t.deg + 2
  match (List.range n).reverse.find? (fun k => le (Z (TM.Term.ofNat k)) t) with
  | some k => if k + 1 == n then none else some (k + 1)
  | none => some 0

/-- 底 w の CNF の組 (a, c) から、`collapse u` の引数 x の成分を組み立てる:
    `w^a·c = ω^(w·a + r)` を c の各項 `ω^r` について。`wcnf` のちょうど逆である。 -/
def xOf (w : Term) (prs : List (Term × Term)) : Term :=
  ofList (prs.flatMap fun ac =>
    (toList ac.2).map fun q => omegaNF (plus (mulL w ac.1) (logOm q)))

/-- `collapse u` の強臨界枝を逆に読む。`i = (Δ₁⊖1) + Δ₂ + …`、`Δⱼ = w^(aⱼ⊖w)·cⱼ` なので、
    `wcnf w (1+i)` の組がそのまま `(aⱼ⊖w, cⱼ)` である。多重度は `a` ではなく `c` に入る
    — 最初に `a` へ入れて表を 8 行外した。

    **尾部 ρ もひとつの組である。** `a = w` ちょうどのとき `Δ = w^0·c = c` は w 未満に
    落ち、`wcnf` はそれを組ではなく尾部として返す。つまり尾部は組 `(w, ρ)` であり、
    それを捨てていたのが `Γ_{ψ₀(Ω₂)+1} = ψ_Ω(Z1+1)` が `none` だった理由。こう読むと
    `i < w` の場合 (組が無く尾部が 1+i) も同じ式になるので、枝は 1 本でよい。 -/
def scPairs (w i : Term) : List (Term × Term) :=
  let (ps, tl) := wcnf w (toList (plus TM.Term.one i))
  ps.map (fun ac => (plus w ac.1, ac.2)) ++ (if tl == zero then [] else [(w, tl)])

/-- `collapse u` の畳み込みの値 V を、それを作った組の列に戻す。

    畳み込みは `acc := φ(a, base + (c⊖1))` で始まり `acc := φ(a, acc + c)` と重なるので、
    **β° の頭が前段の値なら、そこで切って残りが係数である**。切らずに β° 全部を係数と
    読んでも `dict` の値は合う (`dict` は単射でない) が、出てくる Buchholz 項が標準形に
    ならない: `ε_{ζ₀+1} = φ̄(1,ζ₀)` は切れば `ψ₀(Ω²+Ω)`、切らなければ `ψ₀(Ω·(ζ₀+1))` で、
    後者は `G₀` の条件を満たさない。表の 14 行がそれだった。

    前段の値と読めるのは、指数が今の a より大きい組の値だけである: `φ̄(a₁,·)` で a < a₁、
    または強臨界枝の `ψ_{Z u}(·)` (指数は w 以上なので必ず大きい)。 -/
def vebPairs (u : Nat) : Nat → Term → Option (List (Term × Term))
  | 0, _ => none
  | _+1, .psi (.Z d) i => if natOfT d == some u then some (scPairs (Z d) i) else none
  | f+1, .phi a b =>
      if a == zero then none
      else
        -- 意味上の第 2 引数 (β° of [R91] 2.7)。φ̄ は不動点を飛ばすので b そのものではない。
        -- ここを b にすると φ̄(1,ζ₀) 型の行が全部落ちる (今日 3 度目の同じ罠)。
        let bs := if phiShifted a b then plus b TM.Term.one else b
        -- 第 1 の組として読む。u = 0 なら base = 0 なので β° 全部が c⊖1。
        -- u ≥ 1 なら base = reg u + 1 で、`plus base cc` は cc の頭が 1 より大きいと
        -- "+1" を、reg u より大きいと base ごと呑むから、剥がし方は頭で決まる:
        --   頭 = reg u  → 剥がす      頭 > reg u  → base は呑まれている。bs がそのまま c
        --   頭 < reg u  → base を通っていない。この枝の値ではない
        -- c = 0 も届いていない印である (c = 1 + cc ≥ 1)。確かめずに剥がすと φ̄(Ω,0) や
        -- φ̄(Z1,Γ₀) — Veblen 枝が届かない項 — に誤答を返す (Ω より上の母集団で 15 件)。
        -- u = 0 側の除外は別の理由: a ∈ SC のとき φ̄(a,0) は a 自身を表す冗長な項で
        -- ([R91] 2.6(vi) 末尾、`phiNFdefault` がそう畳む)、`dict` は決して出さない。
        let first : Option (List (Term × Term)) :=
          if u == 0 then
            (if b == zero && a.isSC then none else some [(a, plus TM.Term.one bs)])
          else
            match toList bs with
            | [] => none
            | q :: rest =>
              if q == reg u then (let c := ofList rest
                                  if c == zero then none else some [(a, c)])
              else if lt (reg u) q then some [(a, bs)]
              else none
        match toList bs with
        | [] => first
        | h :: rest =>
          let later : Bool := !rest.isEmpty &&
            (match h with
             | .phi a1 _ => !(a1 == zero) && lt a a1
             | .psi (.Z d) _ => natOfT d == some u
             | _ => false)
          if later then
            match vebPairs u f h with
            | some ps => some (ps ++ [(a, ofList rest)])
            | none => first
          else first
  | _+1, _ => none

/-- `dict` の逆。導出は `wcnf`/`collapse` の読みから:
      p = ω^g,  g = w·a + r   ⇒  p = w^a·ω^r
      dict (D (u+1) x) = ω^(reg (u+1) + dict x)
      collapse 0 (Ω^a·c) = φ̄(a, c⊖1)  ⇒  φ̄(a,b) ↦ D 0 (Ω^a·(1+b)) -/
def invF : Nat → Term → Option BT
  | 0, _ => none
  | _+1, .zero => some BT.zero
  | _+1, .Z d => (natOfT d).map (fun u => BT.D (u+1) BT.zero)
  | f+1, .psi (.Z d) i =>
      match natOfT d with
      | none => none
      | some u => (invF f (xOf (Z d) (scPairs (Z d) i))).map (BT.D u)
  | f+1, (.add u v) => ((toList (.add u v)).mapM (invF f)).map BT.ofL
  | f+1, (.phi a b) =>
      if a == zero then
        -- ω 冪。`collapse u` は `omegaNF (reg u + acc + ρ)` を返し、acc は base より
        -- 大きいので reg u は呑まれる。つまり ω 冪の指数の頭が畳み込みの値なら、
        -- **そこで切った残りが `wcnf` の尾部 ρ である**。切らずに指数全部を潰すと値は
        -- 合うが標準形にならない: `ω^(ε₀+1)` は切れば `ψ₀(Ω+1)`、切らなければ
        -- `ψ₀(ε₀+1)` で、後者の `G₀` は Ω を含むので条件を満たさない。
        let g := logOm (.phi a b)
        let split : Option (Nat × List (Term × Term)) :=
          match toList g with
          | h :: _ :: _ =>
            (match h with
             | .psi (.Z d) _ => natOfT d
             | .phi a1 _ => if a1 == zero then none else levelOf h
             | _ => none).bind fun u => (vebPairs u f h).map fun prs => (u, prs)
          | _ => none          -- 尾部が無いなら組も無い (g = 0 を含む)
        match split with
        | some (u, prs) =>
          (invF f (ofList (toList (xOf (Z (TM.Term.ofNat u)) prs)
                           ++ (toList g).tail))).map (BT.D u)
        | none =>
          -- 頭が畳み込みの値でないなら組は無い。Ω 以上なら ω^(Z u + y) で
          -- `D (u+1) (inv y)`、Ω 未満なら ψ₀ そのもの。どの階層かは探す必要がある:
          -- Ω₂ 以上の項に `D 1` を当てると Ω₂ が φ̄(1,Ω) に化ける (表を 6 行外した)。
          if !(lt (.phi a b) (Z .zero)) then
            match levelOf g with
            | some (k+1) => (invF f (subAP (Z (TM.Term.ofNat k)) g)).map (BT.D (k+1))
            | _ => none
          else (invF f g).map (BT.D 0)
      else
        -- `collapse u` の VEBLEN 枝の逆。**階層 u は項から決まる。** ここを u = 0 に
        -- 固定していたのが Ω₂ より上が `none` だった理由で、`φ̄(1,Ω) = ψ₁(Ω₂)` は
        -- この枝の u = 1、最小の例である。
        let t : Term := .phi a b
        match levelOf t with
        | none => none
        | some u =>
          match vebPairs u (f+1) t with
          | none => none
          | some prs => (invF f (xOf (Z (TM.Term.ofNat u)) prs)).map (BT.D u)
  | _+1, _ => none

def dictInv (t : Term) : Option BT := invF (2 * t.deg + 12) t


/-! ## Acceptance record.  Both controls are here: a perturbed target must never match,
    and the `none` count must be printed next to the success count so that "0 wrong" is
    never read as "everything covered". -/

def rt (t : Term) : Bool := match dictInv t with | some b => dict b == t | none => false

private def pool0 : List Term := [zero, TM.Term.one, phi TM.Term.one zero, phi zero TM.Term.one]
private def grow (p : List Term) : List Term :=
  (p ++ (p.flatMap fun x => p.map fun y => phi x y)
     ++ (p.flatMap fun x => p.map fun y => TM.Term.add x y)).eraseDups
def corpus : List Term := (grow (grow pool0)).filter fun t =>
  Evidence.WF.CNV t && !(t == zero)

-- the Veblen fragment: a right inverse, with nothing undefined
#guard corpus.all rt
#guard corpus.all fun t => (dictInv t).isSome
#eval (corpus.length, corpus.countP rt)
-- CTRL a perturbed target must never match
#guard corpus.all fun t => !(match dictInv t with
                             | some b => dict b == TM.Term.add t t
                             | none => false)

/-! ### Above Ω, which is the only region worth adding.  The corpus above is Veblen-only
and therefore says nothing about the clauses that were wrong.  This one is built from
`Z`, `ψ` and `φ̄(·,Ω)` so that both new readings are exercised: the Veblen branch of
`collapse u` for `u ≥ 1`, and the `wcnf` tail. -/

private def poolHi : List Term :=
  [zero, TM.Term.one, Om, Z TM.Term.one, psi Om zero, phi TM.Term.one Om]
private def growHi (p : List Term) : List Term :=
  (p ++ (p.flatMap fun x => p.map fun y => phi x y)
     ++ (p.flatMap fun x => p.map fun y => psi (Z x) y)
     ++ (p.flatMap fun x => p.map fun y => TM.Term.add x y)).eraseDups
def corpusHi : List Term := (growHi poolHi).filter fun t => TM.Term.inT t && !(t == zero)

-- `dict` is not onto 𝔗(M), so `none` is the honest answer on part of this corpus (the
-- rejected shapes are listed below); what must never happen is a WRONG answer.
#guard corpusHi.all fun t => rt t || (dictInv t).isNone
#eval (corpusHi.length, corpusHi.countP rt, corpusHi.countP fun t => (dictInv t).isNone)
#eval ((corpusHi.filter fun t => (dictInv t).isNone).take 8).map (·.toStr)
-- CTRL the same perturbation, above Ω
#guard corpusHi.all fun t => !(match dictInv t with
                               | some b => dict b == TM.Term.add t t
                               | none => false)
-- CTRL the fuel is not what produces the `none`s: ten times as much changes no answer.
#guard corpus.all fun t => invF (20 * t.deg + 120) t == dictInv t
#guard corpusHi.all fun t => invF (20 * t.deg + 120) t == dictInv t
#guard Rows.rows.all fun r => invF (20 * r.t.deg + 120) r.t == dictInv r.t

/-! ### The two clauses that used to be missing, pinned by name.
`φ̄(1,Ω) = ψ₁(Ω₂)` is the smallest ε-number strictly between `Z 0` and `Z 1` that is not
of the form `ω^(Z 0 + y)`; it is the whole reason the level `u` has to be read off the
term.  `ψ_Ω(Z1+1)` is the smallest place where `wcnf` reports a nonempty tail. -/

#guard dictInv (phi TM.Term.one Om) == some (BT.D 1 (BT.Om 2))
#guard dict (BT.D 1 (BT.Om 2)) == phi TM.Term.one Om
#guard dictInv (psi Om (plus (Z TM.Term.one) TM.Term.one))
       == some (BT.D 0 (BT.add (BT.Om 2) (BT.D 1 (BT.D 1 (BT.Om 1)))))
-- CTRL the level must be READ, not assumed: `φ̄(1,Ω)` and `φ̄(1,0)` differ only in the
-- level, and a version that fixed `u = 0` returned `none` on the first and this on the second.
#guard dictInv (phi TM.Term.one zero) == some (BT.D 0 (BT.Om 1))

/-! ### The level search has no silent ceiling.
A constant bound of 8 translated `ψ₉(Ω₁₀) = φ̄(1,Z8)` to `φ̄(1,Z7)` — a WRONG answer, not a
`none`, which is the one thing the scope claim must never allow.  `levelOf` now takes its
bound from the term and refuses when the bound is reached, so the ceiling is visible on
both sides: numeral `Z` indices go through, and a non-numeral one (`Z ω`, which `dict`
cannot produce) comes back `none` instead of being rounded down to the largest numeral. -/

#guard ((List.range 13).drop 1).all fun u =>
  dictInv (dict (BT.D u (BT.Om (u+1)))) == some (BT.D u (BT.Om (u+1)))
#guard ((List.range 13).drop 1).all fun u => dictInv (dict (BT.D u BT.one)) == some (BT.D u BT.one)
-- the exact term the constant bound got wrong
#guard dictInv (phi TM.Term.one (Z (TM.Term.ofNat 8))) == some (BT.D 9 (BT.Om 10))
-- CTRL above the numerals there is nothing to find, and it says so
#guard dictInv (Z TM.Term.omega) == none
#guard dictInv (psi (Z TM.Term.omega) zero) == none
#guard dictInv (phi TM.Term.one (Z TM.Term.omega)) == none

-- the table: every row, including the `(0,0)(1,1)(2,2)` region the table warns about
#guard Rows.rows.all fun r => rt r.t
#eval (Rows.rows.countP fun r => rt r.t,
       Rows.rows.countP fun r => (dictInv r.t).isNone,
       Rows.rows.length)
#eval (Rows.rows.filter fun r => !(rt r.t) && (dictInv r.t).isSome).map fun r =>
  (r.name, r.t.toStr, ((dictInv r.t).map fun b => (dict b).toStr).getD "?")
-- and the answers are STANDARD Buchholz terms, not merely terms that `dict` maps back.
-- This is the guard that forced the fold to be peeled apart rather than read as one pair:
-- fourteen rows came back as value-correct non-standard terms before it was added.
-- **5 行だけ例外で、数で固定してある。** すべて diff.md の族 2 と族 3、つまり外部の表と
-- 食い違う行である。形は `φ̄(1, φ̄(1,ζ₀)+…)` と `φ̄(1,φ̄(1,φ̄(0,φ̄(0,ζ₀))))` で、β° の頭が
-- 今の第 1 引数より大きい指数の値になっていないので剥がす切れ目が無く、第 1 の組として
-- 読むしかない。**値は正しい** (`rt` は 60/60 通る) が標準形にならない。剥がしとは別の
-- 考えが要るので直していない。数が動けばここが落ちる。
#guard (Rows.rows.countP fun r => match dictInv r.t with
        | some b => BT.isStd b | none => false) == Rows.rows.length - 5
#eval (Rows.rows.filter fun r => !(match dictInv r.t with
        | some b => BT.isStd b | none => false)).map fun r => r.name

-- the other direction, from the BT side
private def seeds : List BT := [BT.zero, BT.one, BT.Om 1, BT.Om 2, BT.omega]
private def bgrow (p : List BT) : List BT :=
  (p ++ (p.flatMap fun x => [BT.D 0 x, BT.D 1 x, BT.D 2 x])
     ++ (p.flatMap fun x => p.map fun y => BT.add x y)).eraseDups
def btPool : List BT := (bgrow (bgrow seeds)).filter BT.isStd
-- **`dictInv ∘ dict = id` on the nose**, term for term, not merely as values.  It was
-- 328/336 as long as the fold was read as a single pair; peeling the fold made the other
-- eight exact as well, which is the same defect the `isStd` guard above catches.
#guard btPool.all fun b => dictInv (dict b) == some b
#eval (btPool.length, btPool.countP fun b => dictInv (dict b) == some b)
-- CTRL the pool must reach the new region: `D 2` terms, and terms whose `dict` is ≥ Ω.
#eval (btPool.countP fun b => !(lt (dict b) Om), btPool.countP fun b => !(lt (dict b) (Z TM.Term.one)))

/-! ### How far the [R91] 2.7 gap reaches.

`TM/FS.lean`'s `phiShifted` transcribes 2.7 literally, and the note there records why the
second disjunct ought to be `a.isSC` rather than `b == zero && a.isSC` — taken literally
2.7 sends φ̄α0 and φ̄α1 to the same ordinal for α ∈ SC.  This file is the only one that can
see the table, both corpora and a pool of `dict` values at once, so the reach is measured
here.  The two readings differ exactly on φ̄(A,B) with A ∈ SC and B ≠ 0.

`dict` ITSELF IS UNTOUCHED: its only route to `phiShifted` is `logOm`'s `phi zero b`
clause, and at `a = 0` the two readings coincide because `0 ∉ SC`.  `dictInv` and `fsN`
do call it with a general first argument, so they are the ones that would move. -/

#guard (zero : Term).isSC == false     -- why `dict` cannot see the gap

private def sh2 (a b : Term) : Bool := isFP a (splitFin b).1 || a.isSC
private def splits : Term → Bool
  | phi a b => phiShifted a b != sh2 a b
  | _ => false
private def subterms : Term → List Term
  | .add a b => .add a b :: (subterms a ++ subterms b)
  | .omg a => .omg a :: subterms a
  | .phi a b => .phi a b :: (subterms a ++ subterms b)
  | .psi k a => .psi k a :: (subterms k ++ subterms a)
  | .Z a => .Z a :: subterms a
  | t => [t]

-- out of reach: no table row, no CNV-corpus term, no value in the 336-term `dict` pool
#guard Rows.rows.all fun r => !((subterms r.t).any splits)
#guard corpus.all fun t => !((subterms t).any splits)
#guard btPool.all fun b => !((subterms (dict b)).any splits)
-- CTRL the test is not vacuous, and the reach is stated honestly: above Ω the shape
-- occurs in 12 of 89 terms, and 4 of those 12 DO have a Buchholz preimage — so the gap
-- is inside `dict`'s image, merely above everything R1 measures.
#eval (corpusHi.length, corpusHi.countP fun t => (subterms t).any splits,
       corpusHi.countP splits, (corpusHi.filter splits).countP fun t => (dictInv t).isSome)
#eval (corpusHi.filter fun t => splits t && (dictInv t).isSome).map (·.toStr)

end Dict
end Trans
