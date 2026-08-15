# 補足

[table-r1.md](table-r1.md) の本筋から外したもの。**表を読むのに要らない。**

- $`\mathrm{RawCertified}`$ — $`\mathfrak{T}(M)`$ の条件を落とした関係。
  [E.cert](table-r1.md#ecert) がなぜその条件を要求するのかを見るためのもの
- $`f_n`$ 印が何を言っているか
- [E.cert](table-r1.md#ecert) が言っていないこと
- ✅ の付いた行について追加で言えること (T.unique / T.bound / T.eps0)
- $`\mathcal{T}`$ — 形成条件を課す前の項の全体 (D.Term)
- [D.Cl](table-r1.md#dcl) の読み方 — $`\forall f`$ が規則の族であること
- [D.TM](table-r1.md#dtm) の読み方 — Rathjen 表記の標準形、$`Z`$ の出自、$`\bar\varphi`$ の不動点

## D.Term

**Rathjen の項**の全体 $`\mathcal{T}`$ を、次の文法が生成する式の集合と定義する。
形成条件は課さない — 課したものが [D.TM](table-r1.md#dtm) である。

```math
\alpha, \beta \;::=\;
0 \;\mid\; M \;\mid\; \alpha \oplus \beta \;\mid\;
\bar\omega^{\alpha} \;\mid\; \bar\varphi(\alpha, \beta) \;\mid\;
\psi_{\alpha}(\beta) \;\mid\; Z(\alpha)
```

$`M`$ は最小の弱 Mahlo 基数を表す定数である。

## D.RawCertified

**制限なしの証明書** $`\mathrm{RawCertified} \subseteq \mathcal{S} \times \mathcal{T}`$ を、
[D.Certified](table-r1.md#dcertified) の 3 規則から $`\in \mathfrak{T}(M)`$ の前提を
落とした関係と定義する。値は $`\mathcal{T}`$ のどこにあってもよい。

```math
\mathrm{RawCertified} \;\subseteq\; \mathcal{S} \times \mathcal{T}
```

含意は片側だけである。

```math
\mathrm{Certified}(S, t) \;\Longrightarrow\; \mathrm{RawCertified}(S, t)
\qquad\qquad
\mathrm{RawCertified}(S, t) \;\not\Longrightarrow\; \mathrm{Certified}(S, t)
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
$`\forall n.\;\mathrm{Certified}(S[n], f_n)`$ の**値の側だけ**を言う。

```math
\forall n.\; r(S[n]) = \mathrm{fsN}(t, k(n))
```

$`r`$ は読み手で、行によって `o?` か `oR` である (両方が定義される所では一致する)。
$`\mathrm{fsN}(t, \cdot)`$ は $`\mathfrak{T}(M)`$ 側の基本列、$`k`$ はその行の添字で
**行ごとに違う** (一律に $`n+1`$ ではない)。有限個の $`n`$ を試したのではなく、
すべての $`n`$ についての定理である。

**$`S[n]`$ がその値を認証することは言っていない。** 上の前提が要求するのは後者であり、
残る 3 前提は手つかずである。E.fs は E.cert の材料の一部であって、E.cert に近いことを
意味しない。

## E.cert が言っていないこと

[D.Certified.lim](table-r1.md#dcertifiedlim) の共終性の前提と $`f_n \lt t`$・$`f_n \lt f_{n+1}`$
から $`\sup_n f_n = t`$ が出る。$`\mathfrak{T}(M)`$ 側の共終性は証明の中にある。

言っていないのは BMS 側である:

```math
\sup_n |S[n]| = |S|
```

これが無いと $`\sup_n f_n = t`$ から $`|S| = t`$ へ渡れない。そしてこのリポジトリに
$`|S[n]| \lt |S|`$ も展開列の共終性も**補題として存在しない**。BMS を順序数表記として
読むとき極限行の値が展開の上限であることは**読み方の定義**であって定理ではないからである。
E.cert はこの読み方を仮定した上で $`\mathfrak{T}(M)`$ 側を尽くしている。

## T.unique

導出に現れる値がすべて $`\mathfrak{T}(M)`$ の項である範囲では、この行は $`t`$ 以外の
値を取り得ない。上下いずれの側も排除されている。

```math
\forall u.\;\;\mathrm{Certified}(S, u) \;\Longrightarrow\; u = t
```

## T.bound

値が $`\mathfrak{T}(M)`$ の外に出るものも含め、いかなる証明書も $`\omega^{t+1}`$ 以上を
与えない。

```math
\forall u.\;\;\mathrm{RawCertified}(S, u) \;\Longrightarrow\; \bar\varphi(0,\,t+1) \not\le u
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

**この形成条件が Rathjen 表記の標準形の条件を兼ねている。** 和は成分が $`AP`$ で降順のときしか作れず、
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

## D.Cl の読み方

[D.Certified.lim](table-r1.md#dcertifiedlim) の $`\forall f`$ は、$`f`$ ごとに
規則が 1 本ずつあるという意味である ([D.Cl](table-r1.md#dcl) の $`R`$ が規則の族を含む)。

- 規則を使う側 ([T.Cl.closed](table-r1.md#tclclosed)) では、$`f`$ を 1 つ選んで前件を潰す
- 逆向き ([T.Cl.inv](table-r1.md#tclinv)) では、そういう $`f`$ が存在することが言える

**前件は有限とは限らない。** [D.Certified.succ](table-r1.md#dcertifiedsucc) の
$`\forall n \in \mathbb{N}`$ の前件は可算無限個ある。だから「空集合から始めて
有限回ずつ足していく」読み方では届かず、共通部分による定義が要る。

