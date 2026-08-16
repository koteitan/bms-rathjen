import Evidence.RegionV
import Evidence.SqV
/-
Evidence/RegionSeq.lean — the `fsV` half of RegionV §9's comparison

`Evidence/SqV.lean` imports `Evidence/Cert.lean`, and `Cert.lean` will import
`Evidence/RegionV.lean` to assemble the region's certificate.  So RegionV cannot mention
`fsV`, and this file — which nothing on the proof path imports — carries that measurement.
Same reason as SqV's own "the arrow is SqV → Cert and must never reverse".
-/

namespace Evidence.Region

open TM TM.Term

-- `fsV` はずらし 0 で 18 個中 1 個だけ違う (`ψ₀(Ω+ω)`; そこで `fsV` は ε₀+1 を飛ばす)。
#guard seqMiss Evidence.SqV.fsV 0 == 1
#guard seqMiss Evidence.SqV.fsV 1 == 13

/-! ## `Evidence/CNVOps.lean` §26 の三分法と、`ω^·` の狭義単調性

母集団は `SqV` の `cnvAll` に領域の値を足したもの。§26 の等式は定理なので測定は
**対照が発火しているか**のためにある — 3 つの枝が 76 / 10 / 376 で、どれも空ではない。

単調性は **まだ定理ではない**。462 個の総当たり (約 21 万組) で 0 失敗という測定であり、
`Evidence/RegionV.lean` §15.4 の `OmegaLim` が要求するものの半分である。 -/

def cnvCorpus : List Term :=
  (Evidence.SqV.cnvAll
    ++ (argCorpus.map argVal)
    ++ (closureCorpus.map sumVal)).eraseDups.filter Evidence.WF.CNV

#guard cnvCorpus.length == 462
-- 三分法 (定理 `omegaNF_eq` の測定側)。
#guard cnvCorpus.all fun x =>
  omegaNF x == (if Evidence.WF.isFixP x then x else phi zero (Evidence.WF.dnArg x))
-- 3 つの枝はどれも空ではない。
#guard (cnvCorpus.filter Evidence.WF.isFixP).length == 76
#guard (cnvCorpus.filter fun x =>
  !Evidence.WF.isFixP x && Evidence.WF.dnArg x != x).length == 10
#guard (cnvCorpus.filter fun x =>
  !Evidence.WF.isFixP x && Evidence.WF.dnArg x == x).length == 376
-- `ω^·` の狭義単調性 — `CNVOps` §27 で `DnFacts` から出る。総当たりでも 0 失敗。
#guard (cnvCorpus.flatMap fun x => cnvCorpus.filter fun y =>
  lt x y && !(lt (omegaNF x) (omegaNF y))).length == 0

/-! ### `DnFacts` の 3 つ (`CNVOps` §27)

どれも `splitFin` が末尾の `1` をどこに置くかの話で、`ω^·` の話ではない。 -/

-- D1: `dnArg` は下げるだけ。
#guard cnvCorpus.all fun x => le (Evidence.WF.dnArg x) x
-- D2: `x < y` なら `x ≤ dnArg y` — 下げるのは高々 1。
#guard (cnvCorpus.flatMap fun x => cnvCorpus.filter fun y =>
  lt x y && !(le x (Evidence.WF.dnArg y))).length == 0
-- D3: `x` が不動点でなければ `dnArg` は 2 つを潰さない。
#guard (cnvCorpus.flatMap fun x => cnvCorpus.filter fun y =>
  !Evidence.WF.isFixP x && lt x y && Evidence.WF.dnArg x == Evidence.WF.dnArg y).length == 0
-- 対照: `dnArg x ≠ x` が 10 件、`lt` の組が 106491 組。D2/D3 は空虚ではない。
#guard (cnvCorpus.filter fun x => Evidence.WF.dnArg x != x).length == 10
#guard (cnvCorpus.flatMap fun x => cnvCorpus.filter fun y => lt x y).length == 106491
-- `CNVOps` §27 で証明済みの `z < φ̄(0,z)` も、母集団で確認しておく。
#guard cnvCorpus.all fun z => lt z (phi zero z)

end Evidence.Region
