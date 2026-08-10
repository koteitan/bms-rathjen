# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.2.4

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応。

**証明列 ✅ の意味は下の [エビデンス](#エビデンス) を、設計の手順と失敗の記録は
[plan/](../plan/) を参照。**

## 対応表

| BMS | $`T(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L92) | $`0`$ | $`0`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L94) | $`1`$ | $`1`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L95) | $`2`$ | $`2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L96) | $`\omega`$ | $`\omega`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L98) | $`\omega+\omega`$ | $`\omega\cdot 2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L100) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L102) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L104) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\varepsilon_0`$ |  | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明 |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L107) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| [`(0,0)(1,1)(0,0)`](../lean/Rows/TM.lean#L109) | $`\bar{\varphi}(1,0)+1`$ | $`\varepsilon_0+1`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L111) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L113) | $`\bar{\varphi}(1,1)`$ | $`\varepsilon_1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L115) | $`\bar{\varphi}(1,\omega)`$ | $`\varepsilon_\omega`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(0,0)`](../lean/Rows/TM.lean#L117) | $`\bar{\varphi}(1,\omega)+1`$ | $`\varepsilon_\omega+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(2,0)`](../lean/Rows/TM.lean#L119) | $`\bar{\varphi}(1,\bar{\varphi}(0,2))`$ | $`\varepsilon_{\omega^2}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,0)`](../lean/Rows/TM.lean#L121) | $`\bar{\varphi}(1,\bar{\varphi}(0,\omega))`$ | $`\varepsilon_{\omega^\omega}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L124) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\varepsilon_{\varepsilon_0}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L126) | $`\bar{\varphi}(2,0)`$ | $`\zeta_0`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(0,0)`](../lean/Rows/TM.lean#L128) | $`\bar{\varphi}(2,0)+1`$ | $`\zeta_0+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,0)`](../lean/Rows/TM.lean#L130) | $`\bar{\varphi}(0,\bar{\varphi}(2,0))`$ | $`\omega^{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,1)`](../lean/Rows/TM.lean#L132) | $`\bar{\varphi}(1,\bar{\varphi}(2,0))`$ | $`\varepsilon_{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(2,0)`](../lean/Rows/TM.lean#L139) | $`\bar{\varphi}(2,\omega)`$ | $`\zeta_\omega`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ε_{ζ₀·ω} を訂正 (較正事故) |
| [`(0,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L142) | $`\bar{\varphi}(3,0)`$ | $`\bar{\varphi}(3,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ₁ を訂正 (較正事故の初検出行) |
| [`(0,0)(1,1)(2,1)(3,0)`](../lean/Rows/TM.lean#L145) | $`\bar{\varphi}(\omega,0)`$ | $`\bar{\varphi}(\omega,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ_ω を訂正 |
| [`(0,0)(1,1)(2,1)(3,0)(4,1)`](../lean/Rows/TM.lean#L147) | $`\bar{\varphi}(\bar{\varphi}(1,0),0)`$ | $`\bar{\varphi}(\varepsilon_0,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ_{ε₀} を訂正 |
| [`(0,0)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L149) | $`\psi_{\Omega}(0)`$ | $`\Gamma_0`$ |  | [oR](../lean/Trans/Recal.lean) | ψ 項の初登場。旧値 φ̄(3,0) を訂正 |
| [`(0,0)(1,1)(2,1)(3,1)(0,0)`](../lean/Rows/TM.lean#L152) | $`\psi_{\Omega}(0)+1`$ | $`\Gamma_0+1`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,1)(3,1)(1,0)`](../lean/Rows/TM.lean#L154) | $`\bar{\varphi}(0,\psi_{\Omega}(0))`$ | $`\omega^{\Gamma_0+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)`](../lean/Rows/TM.lean#L166) | $`\psi_{\Omega}(Z(1))`$ | $`\psi_0(\Omega_2)`$ |  | [oR](../lean/Trans/Recal.lean) | 行 1 に 2 が現れる最初の行。旧値 φ̄(ω,0) を訂正 |
| [`(0,0)(1,1)(2,2)(1,1)`](../lean/Rows/TM.lean#L169) | $`\bar{\varphi}(1,\psi_{\Omega}(Z(1)))`$ | $`\varepsilon_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)`](../lean/Rows/TM.lean#L172) | $`\bar{\varphi}(2,\psi_{\Omega}(Z(1)))`$ | $`\zeta_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L175) | $`\psi_{\Omega}(Z(1)+1)`$ | $`\Gamma_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L178) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L181) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2)\cdot 2)`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)`](../lean/Rows/TM.lean#L185) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+1))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(2,0)`](../lean/Rows/TM.lean#L189) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+1))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,0)`](../lean/Rows/TM.lean#L193) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\omega))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)`](../lean/Rows/TM.lean#L197) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\varepsilon_0))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)(4,2)`](../lean/Rows/TM.lean#L201) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\psi_{\Omega}(Z(1))))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_0(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)`](../lean/Rows/TM.lean#L206) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\Omega_1))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(2,1)`](../lean/Rows/TM.lean#L210) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega+\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\Omega_1\cdot 2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,1)`](../lean/Rows/TM.lean#L214) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(0,\Omega+\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_1(\Omega_1)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,2)`](../lean/Rows/TM.lean#L219) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_1(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,2)`](../lean/Rows/TM.lean#L224) | $`\psi_{\Omega}(Z(1)+Z(1))`$ | $`\psi_0(\Omega_2\cdot 2)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 φ̄(ω²,0) を訂正 |
| [`(0,0)(1,1)(2,2)(2,2)(2,2)`](../lean/Rows/TM.lean#L227) | $`\psi_{\Omega}(Z(1)+Z(1)+Z(1))`$ | $`\psi_0(\Omega_2\cdot 3)`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)`](../lean/Rows/TM.lean#L231) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)))`$ | $`\psi_0(\psi_2(1))`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 φ̄(ω^ω,0) を訂正 |
| [`(0,0)(1,1)(2,2)(3,0)(3,0)`](../lean/Rows/TM.lean#L234) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+1))`$ | $`\psi_0(\psi_2(2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,0)`](../lean/Rows/TM.lean#L237) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\omega))`$ | $`\psi_0(\psi_2(\omega))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)`](../lean/Rows/TM.lean#L240) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\bar{\varphi}(1,0)))`$ | $`\psi_0(\psi_2(\varepsilon_0))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)`](../lean/Rows/TM.lean#L243) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\psi_{\Omega}(Z(1))))`$ | $`\psi_0(\psi_2(\psi_0(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,1)`](../lean/Rows/TM.lean#L247) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\Omega))`$ | $`\psi_0(\psi_2(\Omega_1))`$ |  | [oR](../lean/Trans/Recal.lean) |  |

# エビデンス

対応表の 1 行 $`(M, t)`$ が主張していることを、**主張の強い順**に並べる。
`E.` は行についての命題、`P.` はその補助命題、`D.` は定義。
**証明済みかどうかは各節に明記する** — 表に載っていることと証明されていることは
別である。

- [E.otype — 行の主張そのもの](#eotype--行の主張そのもの)
- [E.certified — ✅ の実体](#ecertified--✅-の実体)
- [E.cofinal — 展開と基本列の相互共終](#ecofinal--展開と基本列の相互共終)
- [E.ground — 各表記系だけの構造](#eground--各表記系だけの構造)
- [E.embed — 順序埋め込み](#eembed--順序埋め込み)
- [E.trans — 単一アルゴリズムの出力であること](#etrans--単一アルゴリズムの出力であること)
- [証明書の強さと、その限界](#証明書の強さとその限界)
- [定義](#定義)

## E.otype — 行の主張そのもの

$`<_B`$ を BMS の順序、$`<_T`$ を $`\mathfrak{T}(M)`$ の順序、$`\mathrm{Std}`$ を
標準形、$`\mathrm{NF}`$ を正規形とする。$`<_T`$ の $`\mathrm{NF}`$ 上への制限が
整礎であるという仮定を $`\mathrm{wf}`$ と書く。**行 $`(M,t)`$ の主張は**:

```math
\mathrm{wf} \;\Longrightarrow\;
\mathrm{otype}\bigl(\{\,N : \mathrm{Std}(N),\ N <_B M \,\},\ <_B\bigr)
\;=\;
\mathrm{otype}\bigl(\{\, s \in \mathrm{NF} : s <_T t \,\},\ <_T\bigr)
```

$`\mathrm{otype}(X, <)`$ は整列順序集合 $`(X, <)`$ に順序同型な順序数を返す関数。

**状態: 未証明。** mathlib (順序型) が要り、$`\mathrm{wf}`$ は仮定として切り出す
(紙の上では Rathjen 1994 の整列証明として既知)。以下の E は、これを支えるため、
あるいはこれを迂回して同じことを言うために立てられている。

## E.certified — ✅ の実体

$`\mathrm{otype}`$ を直接扱う代わりに、**展開の再帰だけ**で同じことを述べたもの:

```math
\mathrm{Certified}\;M\;t
```

$`o`$ にも順序型にも言及せず、$`M`$ の展開木を根から $`[\,]`$ / $`0`$ まで降りる
導出の存在を要求する ([D.Certified](#dcertified))。**表の ✅ 列はこれが存在する行
にだけ機械的に付く。**

**状態: 11 行で証明済み。** 較正事故のあと、$`o`$ に言及しない形へ移した結果である
— $`o`$ を含む主張は $`o`$ が誤っていれば道連れになる。

## E.cofinal — 展開と基本列の相互共終

BMS の展開列と $`\mathfrak{T}(M)`$ の基本列は、**同じ順序数への異なる共終列**に
なり得る (例: $`\varepsilon_1`$ へ BMS は
$`\varepsilon_0, \varepsilon_0^2, \varepsilon_0^{\varepsilon_0},\dots`$ で登り、
標準の基本列は $`\varepsilon_0{+}1, \omega^{\varepsilon_0+1},\dots`$ で登る)。
そこで等式ではなく相互共終で立てる。行 $`(M,t)`$ について:

```math
\forall n.\ o(M[n]) <_T t,
\qquad
\forall n\,\exists k.\ o(M[n]) <_T t[k],
\qquad
\forall k\,\exists n.\ t[k] <_T o(M[n])
```

両側が互いに追い越し合えば上限は一致するので、**$`M`$ と $`t`$ が同じ極限を指す**。
$`\varepsilon_0`$ 以下では添字ずれを除いた等式 $`o(M[n]) = o(M)[n{+}1]`$ が
そのまま成り立つ。

**状態: 行ごとに証明済みのものがある。** ただし添字のずれは**行ごとに違う** —
測定では $`n{+}1`$ が 4 行、$`n{+}2`$ が 1 行、$`n`$ が 2 行、専用が 2 行。
一様な $`{+}1`$ は誤り。

## E.ground — 各表記系だけの構造

E 群が $`o`$ に言及するのに対し、これは**片側だけ**の性質で、対応表が正しいか
否かに依らず各表記系が持つべき土台である。

$`\mathfrak{T}(M)`$ 側 — 極限の正規形 $`t`$ と任意の $`s \in \mathrm{NF}`$:

```math
t[n] <_T t,
\qquad
s <_T t \implies \exists n.\ s <_T t[n]
```

BMS 側 — 標準形の $`M, N`$:

```math
M[n] <_B M,
\qquad
N <_B M \implies \exists n.\ N <_B M[n]
```

**状態: 部分的。** $`\mathfrak{T}(M)`$ 側の共終性は証明書の中で行ごとに使われている。

## E.embed — 順序埋め込み

標準形の $`M, N`$ について:

```math
o(M) \in \mathrm{NF},
\qquad
M <_B N \iff o(M) <_T o(N)
```

**状態: 一般形は未証明。** 順序は決定可能なので、個別のペアは計算で即検査できる。

## E.trans — 単一アルゴリズムの出力であること

```math
o(M) = t
```

**これ自体は $`o`$ の正しさを主張しない。**「全行が 1 つの $`o`$ から機械的に出た」
ことだけを言う。**較正事故はこの検査を全行で通ったまま起きた** — 両辺を同じ写像で
計算する検査は、写像の系統的な誤りを原理的に検出できない。

**状態: 全行で機械検査済み (弱いエビデンス)。**

## 証明書の強さと、その限界

E.certified がこの行について言えることの範囲を、定理として:

**一意性** — 導出に現れる値がすべて $`\mathfrak{T}(M)`$ の項である証明書の範囲では、
この行は $`t`$ 以外の値を取り得ない。上下いずれの側も排除されている。

```math
\forall u.\;\;\mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;u \;\Longrightarrow\; u = t
```

**上限 (無条件)** — 値が $`\mathfrak{T}(M)`$ の外に出るものも含め、いかなる証明書も
$`\omega^{t+1}`$ 以上を与えない。$`\mathrm{DomI}`$ の仮定が無いことに注意。

```math
\forall u.\;\;\mathrm{Certified}\;M\;u \;\Longrightarrow\; \bar\varphi(0,\,t+1) \not\le u
```

**ε₀ 行の鋭い上限** — この行では $`\varepsilon_0`$ の直上から塞がれている。

```math
\forall u.\;\; \varepsilon_0 < u \;\Longrightarrow\;
\neg\,\mathrm{Certified}\;[(0,0)(1,1)]\;u
```

**まだ排除できていないこと** — $`t`$ より**下**の値が、$`\mathfrak{T}(M)`$ の外へ出る
部分値を経由して認証される可能性:

```math
\exists u.\;\; u < t \;\wedge\; \mathrm{Certified}\;M\;u
\;\wedge\; \neg\,\mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;u \;\;?
```

上側は無条件に塞がっているので**残る穴は片側のみ**。P.undershoot_reduction により
葉 1 枚に還元済み:

> **P.T** $`a \le b \to b \le c \to a \le c`$ — 中間項 $`b`$ が
> $`\mathrm{Frag2}`$、**両端点は任意**

P.T は**真だが、このリポジトリの手法では証明できない**。真であること: 1010 項の
掃引で反例 0、結論を反転した陽性対照は 3628 万回発火。証明できないこと: 辞書式
帰納法が両端点の第 1 引数の比較可能性を消費するが、それは $`\mathrm{Frag2}`$ の
外で偽 (P.frag2_stops_at_psi)。端点に $`\mathrm{inT}`$ を課せば証明できるが、
**開いている場合は $`\mathrm{inT}`$ でない場合**なので適用できない。

## その他の弱いエビデンス

有限個の $`n`$ の計算検査であり、**較正誤りを検出できない**ことが実証されている。

| 記号 | 意味 |
|---|---|
| `o` | E.trans がこの行で成立 |
| `oR` | オラクル較正済みの候補値 (P進大好きbot 氏の変換写像の Lean 移植)。全行一致をビルド時 `#guard` で強制 |
| `bisim6` | 深さ 6 の双模倣 |
| `oStageC` | Stage C の候補翻訳の値の一致 |

# 定義

## D.Certified

$`\mathrm{Certified}\;M\;t`$ は帰納的述語で、導入規則は 3 つ:

```math
\frac{}{\mathrm{Certified}\;[\,]\;0}
\qquad
\frac{\mathrm{kind}\,M = \mathrm{succ}
\qquad \forall n.\;\mathrm{Certified}\;(M[n])\;t}
{\mathrm{Certified}\;M\;(t+1)}
```

```math
\frac{\mathrm{kind}\,M = \mathrm{lim}
\quad \forall n.\;\mathrm{Certified}\;(M[n])\;(f_n)
\quad \forall n.\;f_n < t
\quad \forall n.\;f_n < f_{n+1}
\quad \forall s \in \mathfrak{T}(M).\;s < t \to \exists n.\;s \le f_n}
{\mathrm{Certified}\;M\;t}
```

極限規則の 5 前提のうち**同一性を述べるのは
$`\forall n.\;\mathrm{Certified}\;(M[n])\;(f_n)`$ の 1 つだけ**で、残る 4 つは
列 $`f`$ の性質である。**性質をいくつ検査しても値は決まらない**
([plan/constitutions.md](../plan/constitutions.md) C2)。較正事故はここを取り違えた。
$`f`$ は**パラメータ**であって、特定の基本列に合わせる必要はない。

## D.CertifiedIn / D.DomI

```math
\mathrm{DomI}(t) \;:\equiv\; t \in \mathfrak{T}(M)
```

$`\mathrm{Certified}`$ は認証される値に制約を課さないので、生の項の上では
$`\mathfrak{T}(M)`$ の項でない値も認証されうる (P.cert_not_single_valued):

```math
\mathrm{Certified}\;[(0)(1)]\;\omega
\qquad\text{かつ}\qquad
\mathrm{Certified}\;[(0)(1)]\;(1+M)
```

$`\mathrm{CertifiedIn}\;\mathrm{Dom}`$ は**導出に現れる値すべて**が
$`\mathrm{Dom}`$ に属することを要求する版。E.certified の一意性が
$`\mathrm{DomI}`$ を要求するのは、この一価性の破れを塞ぐためである。

# 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean) ·
[証明書](../lean/Evidence/Cert.lean)
