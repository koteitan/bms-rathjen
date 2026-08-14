# 補足

[table-r1.md](table-r1.md) の本筋から外したもの。**表を読むのに要らない。**

- $`\mathrm{RawCertified}`$ — $`\mathfrak{T}(M)`$ の条件を落とした関係。
  [E.cert](table-r1.md#ecert) がなぜその条件を要求するのかを見るためのもの
- $`f_n`$ 印が何を言っているか
- [E.cert](table-r1.md#ecert) が言っていないこと
- ✅ の付いた行について追加で言えること (T.unique / T.bound / T.eps0)
- [D.TM](table-r1.md#dtm) の読み方 — 正規形、$`Z`$ の出自、$`\bar\varphi`$ の不動点

## D.RawCertified

上の 3 規則から $`\in \mathfrak{T}(M)`$ の前提を落とした 2 項関係。値は
$`\mathcal{T}`$ のどこにあってもよい。

```math
\mathrm{RawCertified} \;\subseteq\; \mathcal{M} \times \mathcal{T}
```

含意は片側だけである。

```math
\mathrm{Certified}(M, t) \;\Longrightarrow\; \mathrm{RawCertified}(M, t)
\qquad\qquad
\mathrm{RawCertified}(M, t) \;\not\Longrightarrow\; \mathrm{Certified}(M, t)
```

$`\mathrm{RawCertified}`$ は**一価ではない**。同じ行列が 2 つの値を取れる:

```math
\mathrm{RawCertified}([(0)(1)], \omega)
\qquad\text{かつ}\qquad
\mathrm{RawCertified}([(0)(1)], 1+M)
```

$`1+M \notin \mathfrak{T}(M)`$ である (和は降順でなければならない、[D.TM](table-r1.md#dtm))。
これが $`\mathrm{Certified}`$ の側に $`\in \mathfrak{T}(M)`$ が要る理由である。

**Lean 側の名前はこの文書と逆なので注意する。** `Evidence/Cert.lean` の
`Certified` がここの $`\mathrm{RawCertified}`$、`CertifiedIn DomI` がここの
$`\mathrm{Certified}`$ に当たる。

## E.fs

弱いエビデンスの $`f_n`$ 印の中身。[D.Certified.lim](table-r1.md#dcertifiedlim) の前提
$`\forall n.\;\mathrm{Certified}(M[n], f_n)`$ の**値の側だけ**を言う。

```math
\forall n.\; r(M[n]) = \mathrm{fsN}(t, k(n))
```

$`r`$ は読み手で、行によって `o?` か `oR` である (両方が定義される所では一致する)。
$`\mathrm{fsN}(t, \cdot)`$ は $`\mathfrak{T}(M)`$ 側の基本列、$`k`$ はその行の添字で
**行ごとに違う** (一律に $`n+1`$ ではない)。有限個の $`n`$ を試したのではなく、
すべての $`n`$ についての定理である。

**$`M[n]`$ がその値を認証することは言っていない。** 上の前提が要求するのは後者であり、
残る 3 前提は手つかずである。E.fs は E.cert の材料の一部であって、E.cert に近いことを
意味しない。

## E.cert が言っていないこと

[D.Certified.lim](table-r1.md#dcertifiedlim) の共終性の前提と $`f_n \lt t`$・$`f_n \lt f_{n+1}`$
から $`\sup_n f_n = t`$ が出る。$`\mathfrak{T}(M)`$ 側の共終性は証明の中にある。

言っていないのは BMS 側である:

```math
\sup_n |M[n]| = |M|
```

これが無いと $`\sup_n f_n = t`$ から $`|M| = t`$ へ渡れない。そしてこのリポジトリに
$`|M[n]| \lt |M|`$ も展開列の共終性も**補題として存在しない**。BMS を順序数表記として
読むとき極限行の値が展開の上限であることは**読み方の定義**であって定理ではないからである。
E.cert はこの読み方を仮定した上で $`\mathfrak{T}(M)`$ 側を尽くしている。

## T.unique

導出に現れる値がすべて $`\mathfrak{T}(M)`$ の項である範囲では、この行は $`t`$ 以外の
値を取り得ない。上下いずれの側も排除されている。

```math
\forall u.\;\;\mathrm{Certified}(M, u) \;\Longrightarrow\; u = t
```

## T.bound

値が $`\mathfrak{T}(M)`$ の外に出るものも含め、いかなる証明書も $`\omega^{t+1}`$ 以上を
与えない。

```math
\forall u.\;\;\mathrm{RawCertified}(M, u) \;\Longrightarrow\; \bar\varphi(0,\,t+1) \not\le u
```

## T.eps0

$`\varepsilon_0`$ の行では、その直上から塞がれている。

```math
\forall u.\;\; \varepsilon_0 < u \;\Longrightarrow\;
\neg\,\mathrm{RawCertified}([(0,0)(1,1)], u)
```

**まだ排除できていないのは片側だけである** — $`t`$ より**下**の値が、
$`\mathfrak{T}(M)`$ の外へ出る部分値を経由して認証される可能性。上側は T.bound が
無条件に塞いでいる。

## D.TM の補足

**この形成条件が正規形の条件を兼ねている。** 和は成分が $`AP`$ で降順のときしか作れず、
$`\psi_\kappa(\alpha)`$ は $`\kappa`$ が正則かつ $`K_\kappa(\alpha) \lt \alpha`$ の
ときしか作れない。だから 1 つの順序数を表す項は 1 つしかない ([Rathjen, 1991] 2.8(i))。

**$`Z`$ は [Rathjen, 1991] 自身の記号である** (2.1(vii))。1990 年の $`T(M)`$ は 2 引数の
$`\chi`$ の階層を持つが、[Rathjen, 1991] はそれを 1 本の $`Z`$ に置き換えた:

```math
Z(\alpha) \;=\; \chi_\alpha(0)
```

**したがって $`\Omega_2 = \chi_0(1)`$ はこの表記系では書けない。** $`\chi`$ の第 2 引数が
$`\Omega`$ 階層を枚挙するのに、それが 0 に固定されているからである。$`Z(1)`$ は
$`\chi_1(0)`$、すなわち最小の弱到達不能基数 $`I`$ であって $`\Omega_2`$ ではない
([値についての注意](table-r1.md#値についての注意))。

**$`\bar\varphi`$ は $`\omega^\cdot`$ の不動点を飛ばして数える** ([Rathjen, 1991] 2.6(vi))。
$`\bar\varphi(0,\beta)`$ は最初の不動点未満では $`\omega^\beta`$ だが、

```math
\bar\varphi(0, \varepsilon_0) = \omega^{\varepsilon_0 + 1} \ne \varepsilon_0
```

**不動点の下では 2 つの読みが一致するので、そこだけで較正した関数・コーパス・読者は
上で静かに誤る。**
