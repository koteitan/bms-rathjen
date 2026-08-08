/-
Test/TMLinearity.lean — 順序 < の線形性の総当たり検査

[R91] 2.3 の < が (実装した判定手続きの上で) 三分律・推移律・非反射律を
満たすことを、代表的な項の有限集合上で総当たりで確認する。
(一般の証明は Evidence の課題。ここでは実装の健全性チェック。)
-/
import TM

namespace TM.Test
open TM.Term

/-- 検査対象の項 (すべて 𝔗(M) の元) -/
def sample : List Term :=
  let e0 := phi one zero
  let p0 := psi Om zero
  [ zero, one, ofNat 2, omega, plus omega one, add omega omega,
    e0, phi zero e0, phi (ofNat 2) zero, plus e0 omega,
    p0, psi Om one, psi Om p0, plus p0 one,
    Om, Z one, Z omega, Z p0, psi (Z p0) zero,
    M, plus M one, plus M p0, omg (plus M one), omg (plus M omega),
    add (omg (plus M one)) p0 ]

/-- 全要素が形成条件を満たす -/
def allWF : Bool := sample.all inT

/-- 三分律: 相異なる項はちょうど一方向に < -/
def trichotomy : Bool :=
  sample.all fun a => sample.all fun b =>
    if a == b then !(lt a b) && !(lt b a)
    else (lt a b != lt b a)

/-- 非反射律 -/
def irrefl : Bool := sample.all fun a => !(lt a a)

/-- 推移律 -/
def transitive : Bool :=
  sample.all fun a => sample.all fun b => sample.all fun c =>
    !(lt a b) || !(lt b c) || lt a c

#guard allWF
#guard irrefl
#guard trichotomy
#guard transitive

end TM.Test
