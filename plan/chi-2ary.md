# χ を 2 引数に戻す — 検討と、**却下** (2026-08-13)

**結論を先に: R1 の範囲ではこの改修は何も買わない。やらない。**
中心的な根拠が誤っていたので、その訂正ごと残す。実装は無いし、するべきでもない。

**誤っていた根拠。** 「表の $`(0,0)(1,1)(2,2)`$ 以上の行は現在の型では値を書けない」。
書ける。資料が与える値 $`\psi_\Omega(\varepsilon_{\Omega+1})`$ は現行の型で
`inT = true` であり、`dict` の値 $`\psi_\Omega(Z1)`$ より真に小さいことも計算で出る。
そもそも [Rathjen, 1991] の目的は $`\mathfrak{T}(M)`$ が KPM に十分であることなので、
PTO(KPM) 未満の可算順序数はすべて項を持つ。**表の値は最初から書けていた。**

**では何が書けないのか。** $`\Omega_2`$ を「潰す先の正則基数として」名指すこと。
これは可算な値ではなく、翻訳の途中に現れる中間対象である。

**したがって誤りの場所は型ではなく `Trans/Dict.lean` である。** `reg` が

```
reg (u+1) = Z u        -- 「Ω_{u+1} = Z u」というコメントつき
```

と Buchholz の $`\Omega_{u+1}`$ を `Z u` に送っている。`Z 1` は $`\chi_1(0) = I`$ で
あって $`\Omega_2`$ ではないので、$`u \geq 1`$ で誤る。`dict` が compositional に
「引数を写してから潰す」構成であるために $`\Omega_2`$ の名前を要求しており、
$`\mathfrak{T}(M)`$ にはそれが無い。直し方は 2 つある:

```
(a) 型を T(M) に広げて χ を 2 引数にし、compositional な構成を成立させる
(b) 型はそのままで、Ω 階層のところだけ compositional をやめ、
    ψ_0(Ω_u) を正しい 𝔗(M) 項へ直接送る
```

**外部の 3 資料が与える値は (b) の形である。** そして (a) は 1200 箇所を動かして
R1 の範囲では何も増やさない。よって (b) を採る。この文書の以下は、(a) を採る場合に
必要になる数学を記録したものとして残す — 将来 R2 以降で $`\Omega`$ 階層を本当に
潰す必要が出たときのために。

---

## 以下、(a) を採る場合の仕様 (現時点では不要)

## 何が欠けているか (出典つき)

現行の `Term` は [Rathjen, 1991] §2 の $`\mathfrak{T}(M)`$ に忠実であり、そこが問題である。
[Rathjen, 1991] は §2 の前置きでこう書いている:

> $`\mathfrak{T}(M)`$ differs from $`T(M)`$ in some minor aspects:
> 1. The terms $`\Phi\alpha\beta`$ are completely omitted.
> 2. Instead of the hierarchy of functions $`\chi_\nu`$ there is only one function $`Z`$
>    which may be identified with the function $`\alpha \mapsto \chi_\alpha 0`$ of [13].

同じ前置きに、落ちた側が何であるかがはっきり書いてある:

> $`\kappa`$ ranges over regular cardinals $`\lt  M`$ of the shape
> $`\chi_\nu(0)`$ and $`\chi_\nu(\gamma+1)`$

[Rathjen, 1990] 5.1(i) が同じことを定義として述べる:

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

> [Rathjen, 1990] 3.6. Lemma. For every $`\alpha \lt  M^+`$, $`\chi_\alpha : M \to M`$ is a normal
> function with $`\mathrm{dom}(\chi_\alpha) = M`$.

## 順序規則 ([Rathjen, 1990] 3.14, 3.15)

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

**現行の規則は 3.14 の $`\beta = \delta = 0`$ 特殊化である。** [Rathjen, 1991] 2.3.15 は

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
4. `*` と $`K_\kappa`$ を第 2 引数に対応させる ([Rathjen, 1991] 2.2 の対応物を [Rathjen, 1990] から取る)。
5. `TM/FS.lean` の `psiSeed` / `cofT` / `fsN` の `Z` 節。$`\chi_\alpha`$ が正規関数で
   あることから基本列が決まる。
6. 表の $`(0,0)(1,1)(2,2)`$ 以上の値を書き直す。**ここが目的**であり、
   1〜5 はそのための前提である。

## この節は取り消した

ここには「$`\Omega_2`$ 問題を翻訳の側で直してはならない、行き先の型に正しい値が
存在しないのだから」と書いてあった。**逆である。** 正しい値は型の中に存在し、
直す場所は翻訳の側である。冒頭の訂正を見よ。

## 出典

- M. Rathjen, *Ordinal Notations Based on a Weakly Mahlo Cardinal*,
  Archive for Mathematical Logic 29 (1990) 249–263 — 3.6, 3.13, 3.14, 3.15, 5.1
- M. Rathjen, *Proof-theoretic analysis of KPM*,
  Archive for Mathematical Logic 30 (1991) 377–403 — §2 前置き, 2.1, 2.3
- P進大好きbot, *Cheatsheet on Properties of OCFs*,
  <https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Cheatsheet_on_Properties_of_OCFs>
  — $`\chi_0(\alpha) = \Omega_{1+\alpha}`$、$`\chi_1(0) = I`$、$`\psi`$ の制限
