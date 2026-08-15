import Rows.G10

open TM Term BMS Trans Rows Rows.Selected

/-! # 族 4 — 外部の表との突き合わせ

`table/diff.md` の族 4 (先方の表の 326〜328 行目)。族 1〜3 を決めた試験を同じ形で当てる。
**327 は決着し、326 は同じ試験では決められない。** その区別をここに置く。

先方の値は `phi(a,b) = phiNF (1+a) b` で訳した (`table/diff.md` の記法節)。
-/

namespace Rows.Selected
namespace Fam4

/-- 先方の 326 行目の値 `phi(1+1,phi(0,0))`。 -/
def h326 : Term := phiNF (ofNat 3) (phiNF (ofNat 1) zero)
/-- 先方の 327 行目の値 `phi(1+1,phi(1,0))`。 -/
def h327 : Term := phiNF (ofNat 3) (phiNF (ofNat 2) zero)
/-- 先方の 328 行目の値 `phi(1+1,phi(1+1,0))`。 -/
def h328 : Term := phiNF (ofNat 3) (phiNF (ofNat 3) zero)

def t328 : Term := phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
  (add (phi zero (phi zero zero)) (phi zero zero))

def M328 : BMS.Matrix := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1],[2,1]]

-- 3 行とも行 DB の行である
#guard rows.any fun r => r.m==G9.M && r.t==G9.t
#guard rows.any fun r => r.m==G10.M && r.t==G10.t
#guard rows.any fun r => r.m==M328 && r.t==t328

-- 当方と先方は別の値で、先方の値も 𝔗(M) の極限の項である (型や系の違いではない)
#guard [(G9.t,h326),(G10.t,h327),(t328,h328)].all fun p => !(p.1==p.2)
#guard [h326,h327,h328].all fun h => inT h && kindT h==KindT.isLim
-- 3 行とも当方が小さい側
#guard [(G9.t,h326),(G10.t,h327),(t328,h328)].all fun p => lt p.1 p.2 && !(lt p.2 p.1)

/-! ## 先方の値は展開の列を担がない

族 1〜3 を決めた試験。一様なずらしでも、30 項までの探索でも、先方の値の基本列に
展開の像が乗らない。 -/

-- 一様なずらしは 0..11 のどれも成り立たない
#guard [(G9.M,h326),(G10.M,h327),(M328,h328)].all fun p =>
  (List.range 12).all fun k =>
    (List.range 6).any fun n => !(Trans.oR (BMS.expand p.1 n)==some (fsN p.2 (n+k)))

-- 327 と 328: 展開の像は先方の基本列の 0..30 項のどこにも無い
#guard [(G10.M,h327),(M328,h328)].all fun p =>
  (List.range 6).all fun n =>
    (List.range 31).all fun j => !(Trans.oR (BMS.expand p.1 n)==some (fsN p.2 j))

-- 326 だけは 0 番目が偶然当たる。1 番目から先は 30 項まで無い
#guard (List.range 31).any fun j => Trans.oR (BMS.expand G9.M 0)==some (fsN h326 j)
#guard (List.range 5).all fun n =>
  (List.range 31).all fun j => !(Trans.oR (BMS.expand G9.M (n+1))==some (fsN h326 j))

/-! ## CTRL — 同じ試験を当方の値に当てる

**327 と 328 では当たり、326 では当たらない。** 326 の展開の列は標準基本列ではなく
閉じた形 `fA` なので (`Rows/Selected.lean`)、この試験は両側を落とす。乗らないことは
誤りの証拠ではない — `Certified` の極限節は $`f_n`$ が標準基本列であることを要求して
いない — が、**この行についてはこの試験が何も分けない**という事実がここの主題である。 -/

#guard (List.range 6).all fun n => Trans.oR (BMS.expand G10.M n)==some (fsN G10.t (n+1))
#guard (List.range 6).all fun n => Trans.oR (BMS.expand M328 n)==some (fsN t328 (n+1))
#guard (List.range 6).all fun n =>
  (List.range 31).all fun j => !(Trans.oR (BMS.expand G9.M n)==some (fsN G9.t j))
-- 326 の列は閉じた形の方に乗る
#guard (List.range 7).all fun n => Trans.oR (BMS.expand G9.M n)==some (fA n)

/-! ## 327 行目は決着した

当方の値について $`\mathrm{oR}(S[n]) = \mathrm{fsN}(t, n+1)`$ が**全 n について定理**であり
(`G10.oR_M`)、先方の値は上のどの試験も通らない。族 1〜3 と同じ形である。 -/

theorem row327_ours : ∀ n, Trans.oR (BMS.expand G10.M n) = some (fsN G10.t (n+1)) :=
  G10.oR_M

end Fam4
end Rows.Selected
