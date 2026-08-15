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

-- `fsV` はずらし 0 で 18 個中 1 個だけ違う (`ψ₀(Ω+ω)`; そこで `fsV` は ε₀+1 を飛ばす)。
#guard seqMiss Evidence.SqV.fsV 0 == 1
#guard seqMiss Evidence.SqV.fsV 1 == 13

end Evidence.Region
