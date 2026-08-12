# χ を 2 引数に戻す — 仕様 (2026-08-13)

`TM/Terms.lean` の冒頭が記録している欠陥を塞ぐための仕様。**コードより先に数学を固める**
ためのもので、実装はまだ無い。

## 何が欠けているか (出典つき)

現行の `Term` は [R91] §2 の $`\mathfrak{T}(M)`$ に忠実であり、そこが問題である。
[R91] は §2 の前置きでこう書いている:

> $`\mathfrak{T}(M)`$ differs from $`T(M)`$ in some minor aspects:
> 1. The terms $`\Phi\alpha\beta`$ are completely omitted.
> 2. Instead of the hierarchy of functions $`\chi_\nu`$ there is only one function $`Z`$
>    which may be identified with the function $`\alpha \mapsto \chi_\alpha 0`$ of [13].

同じ前置きに、落ちた側が何であるかがはっきり書いてある:

> $`\kappa`$ ranges over regular cardinals $`\lt  M`$ of the shape
> $`\chi_\nu(0)`$ and $`\chi_\nu(\gamma+1)`$

[R90] 5.1(i) が同じことを定義として述べる:

```math
R := \{\chi_\alpha(0) : \alpha < M^+\} \cup \{\chi_\alpha(\beta+1) : \alpha < M^+ \wedge \beta < M\}
```

**したがって $`\Omega_2 = \chi_0(0+1)`$ はちょうど $`\mathfrak{T}(M)`$ が捨てた側にある。**
簡略化は本リポジトリのものではなく Rathjen 自身のもので、`Z 1` を $`\Omega_2`$ と読んで
はならないという `TM/Terms.lean` の注意書きは正しい。

表の $`(0,0)(1,1)(2,2)`$ 以上の行はこの領域にあるので、**現在の型では値を正しく書けない**。

## 直し方は「完全な 2 引数」ではない

第 2 引数は $`0`$ か後続だけでよい (上の 5.1(i))。Cheatsheet の $`\psi`$ の制限
「$`\pi = \chi_\gamma(\delta)`$ で $`\mathrm{cof}(\delta) \leq 1`$」と同じことを言っている。
$`\chi_\alpha`$ は正規関数なので極限の第 2 引数は下から到達でき、名前を要しない:

> [R90] 3.6. Lemma. For every $`\alpha \lt  M^+`$, $`\chi_\alpha : M \to M`$ is a normal
> function with $`\mathrm{dom}(\chi_\alpha) = M`$.

## 順序規則 ([R90] 3.14, 3.15)

$`\mu = \chi_\alpha(\beta)`$、$`\nu =_{NF} \chi_\gamma(\delta)`$ のとき $`\mu \lt  \nu`$ は
次のいずれかと同値:

```math
\begin{aligned}
&1.\quad \alpha < \gamma \ \wedge\ \beta < \nu \ \wedge\ \alpha^* < \nu \cr
&2.\quad \alpha = \gamma \ \wedge\ \beta < \delta \cr
&3.\quad \gamma < \alpha \ \wedge\ (\mu \leq \delta \ \vee\ \mu \leq \gamma^*)
\end{aligned}
```

$`\mu =_{NF} \bar\varphi\alpha\beta \lt  M`$ で $`0 \lt  \alpha`$、$`\nu =_{NF} \chi_\gamma(\delta)`$
のとき:

```math
\mu \neq \nu, \qquad
\mu < \nu \iff (\gamma = 0 \wedge \mu < \delta) \ \vee\ (0 < \gamma \wedge \alpha,\beta < \nu)
```

**現行の規則は 3.14 の $`\beta = \delta = 0`$ 特殊化である。** [R91] 2.3.15 は

```math
Z\alpha < Z\beta \iff (\alpha < \beta \wedge \alpha^* < Z\beta) \ \vee\ (\beta < \alpha \wedge Z\alpha < \beta^*)
```

で、3.14 で $`\beta = \delta = 0`$ と置くと、場合 1 の $`\beta \lt  \nu`$ が自明になり、
場合 2 が消え、場合 3 が $`\mu \leq \gamma^*`$ に落ちる。三つが過不足なく対応するので、
**この移行は現行の振る舞いの一般化であって置き換えではない**。既存の行は
$`\chi_\alpha(0)`$ として保存される。

## 移行の順序

1. **`Term` の `Z (a : Term)` を `Z (a b : Term)` にする。** 意味は $`\chi_a(b)`$。
   `Z a` は機械的に `Z a zero` になる。`Z` の出現は約 1200 箇所だが、
   ほとんどはこの置換で済む。
2. **整形式条件**を `inT` に足す: 第 2 引数は $`0`$ または後続。
3. **`TM/Order.lean` の 2.3.15 を 3.14 に差し替える。** 3.15 ($`\bar\varphi`$ 対 $`\chi`$)
   も要る。ここだけは機械的でない。
4. `*` と $`K_\kappa`$ を第 2 引数に対応させる ([R91] 2.2 の対応物を [R90] から取る)。
5. `TM/FS.lean` の `psiSeed` / `cofT` / `fsN` の `Z` 節。$`\chi_\alpha`$ が正規関数で
   あることから基本列が決まる。
6. 表の $`(0,0)(1,1)(2,2)`$ 以上の値を書き直す。**ここが目的**であり、
   1〜5 はそのための前提である。

## 先にやってはいけないこと

`Trans/Dict.lean` の $`\Omega_2`$ 問題を、型を直す前に「翻訳の側で」直すこと。
`dict` が $`\psi_0(\psi_2(0))`$ を `Z 1` に送るのが資料と食い違うのは翻訳の誤りでは
なく、**行き先の型に正しい値が存在しない**からである。型を直せば
$`\chi_0(1) = \Omega_2`$ が書けるようになり、そこで初めて
「$`\psi_\Omega(\Omega_2)`$ と $`\psi_\Omega(\varepsilon_{\Omega+1})`$ のどちらか」が
翻訳の問題になる。

## 出典

- M. Rathjen, *Ordinal Notations Based on a Weakly Mahlo Cardinal*,
  Archive for Mathematical Logic 29 (1990) 249–263 — 3.6, 3.13, 3.14, 3.15, 5.1
- M. Rathjen, *Proof-theoretic analysis of KPM*,
  Archive for Mathematical Logic 30 (1991) 377–403 — §2 前置き, 2.1, 2.3
- P進大好きbot, *Cheatsheet on Properties of OCFs*,
  <https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Cheatsheet_on_Properties_of_OCFs>
  — $`\chi_0(\alpha) = \Omega_{1+\alpha}`$、$`\chi_1(0) = I`$、$`\psi`$ の制限
