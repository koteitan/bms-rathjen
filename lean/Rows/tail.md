# 証明の仕様

対応表の 1 行 $`(S, t)`$ の証明列に ✅ が付く条件は、これただ 1 つである。

## E.cert

```math
\mathrm{Certified}(S, t)
```

# 定義

## D.Certified

**証明書** $`\mathrm{Certified} \subseteq \mathcal{S} \times \mathfrak{T}(M)`$ を、
次の 3 規則で閉じた最小の関係と定義する。

### D.Certified.zero

```math
\mathrm{Certified}([\;], 0)
```

### D.Certified.succ

```math
\begin{array}{l}
\phantom{{}\land\;} \mathrm{kind}(S) = \text{後続} \cr
{}\land\; \forall n \in \mathbb{N}.\; \mathrm{Certified}(S[n], t) \cr
{}\land\; t+1 \in \mathfrak{T}(M) \cr
{}\longrightarrow\; \mathrm{Certified}(S, t+1)
\end{array}
```

### D.Certified.lim

```math
\forall f : \mathbb{N} \to \mathfrak{T}(M).\;
\left(
\begin{array}{l}
\phantom{{}\land\;} \mathrm{kind}(S) = \text{極限} \cr
{}\land\; t \in \mathfrak{T}(M) \cr
{}\land\; \forall n.\; \mathrm{Certified}(S[n], f_n) \cr
{}\land\; \forall n.\; f_n \lt t \cr
{}\land\; \forall n.\; f_n \lt f_{n+1} \cr
{}\land\; \forall s \in \mathfrak{T}(M).\; s \lt t \;\to\; \exists n.\; s \le f_n \cr
{}\longrightarrow\; \mathrm{Certified}(S, t)
\end{array}
\right)
```

$`\lt`$ は $`\mathfrak{T}(M)`$ の線形順序 ([Rathjen, 1991] 2.3)。

$`\mathrm{Certified}`$ は 3 規則で閉じた**最小の**関係なので、極限行については逆も言える —
$`\mathrm{Certified}(S, t)`$ が成り立つのは、上の 6 条件を満たす $`f`$ が**存在するとき、
かつそのときに限る**。

## D.TM

**Rathjen 表記の標準形** $`\mathfrak{T}(M)`$ を、次の規則で閉じた最小の項集合と
定義する ([Rathjen, 1991] 2.1)。

```math
\frac{}{0 \in \mathfrak{T}(M)}
\qquad
\frac{}{M \in \mathfrak{T}(M)}
\qquad
\frac{\alpha \in \mathfrak{T}(M) \quad M < \alpha}
{\bar\omega^{\alpha} \in \mathfrak{T}(M)}
\qquad
\frac{\alpha \in \mathfrak{T}(M)}{Z(\alpha) \in \mathfrak{T}(M)}
```

```math
\frac{\alpha, \beta \in \mathfrak{T}(M) \quad \alpha, \beta < M}
{\bar\varphi(\alpha, \beta) \in \mathfrak{T}(M)}
\qquad
\frac{\kappa, \alpha \in \mathfrak{T}(M) \quad \kappa \in R
\quad \alpha < M \quad K_\kappa(\alpha) < \alpha}
{\psi_\kappa(\alpha) \in \mathfrak{T}(M)}
```

```math
\frac{\alpha_1, \dots, \alpha_n \in AP \quad n \ge 2
\quad \alpha_n \le \dots \le \alpha_1}
{\alpha_1 \oplus \dots \oplus \alpha_n \in \mathfrak{T}(M)}
```

$`AP`$ は加法的主要、$`SC`$ は強クリティカル、$`R`$ は正則:

```math
AP = \{M\} \cup \{\bar\omega^\alpha\} \cup \{\bar\varphi(\alpha,\beta)\} \cup SC,
\qquad
SC = \{M\} \cup \{\psi_\kappa(\alpha)\} \cup \{Z(\alpha)\},
\qquad
R = \{Z(\alpha)\}
```


## D.Matrix

**バシク行列**の全体 $`\mathcal{S}`$ を、**列** (自然数の有限列) の有限列全体と定義する。

```math
\mathcal{S} \;=\; \bigl(\mathbb{N}^{\ast}\bigr)^{\ast}
```

$`X^{\ast}`$ は $`X`$ の有限列全体を表す。列の本数も列の高さも固定しない。
高さを揃える必要も無い。対応表の行はすべて高さ 2 以下の列からなる。

記号は[数式的定義](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E6%95%B0%E5%BC%8F%E7%9A%84%E5%AE%9A%E7%BE%A9)
に合わせる — 行列を $`S`$、その $`x`$ 番目の列を $`S_x`$、その $`y`$ 成分を $`S_{xy}`$ と書く。
$`M`$ は最小の弱 Mahlo 基数だけを指し、行列には使わない。

## D.expand

**展開** $`S[n]`$ と**行の種別** $`\mathrm{kind}(S)`$ を、次の型の写像と定義する。

```math
\cdot[\cdot] \;:\; \mathcal{S} \times \mathbb{N} \to \mathcal{S}
\qquad\qquad
\mathrm{kind} \;:\; \mathcal{S} \to
\{\text{空}, \text{後続}, \text{極限}\}
```

規則は BM4 の展開規則そのもので、
[koteitan「バシク行列の数式的定義」](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E6%95%B0%E5%BC%8F%E7%9A%84%E5%AE%9A%E7%BE%A9)
に従う。実装は [BMS/Expand.lean](../lean/BMS/Expand.lean)。

# その他の弱いエビデンス

いずれも ✅ の材料であって ✅ ではない。$`f_n`$ 以外は有限個の計算検査であり、
較正誤りを検出できない。

| 記号 | 意味 | 全ての $`n`$? |
|---|---|---|
| $`f_n`$ | [E.fs](misc.md#efs) が Lean の定理 | はい |
| `o` | 翻訳関数がこの行列で定義され $`o(S) = t`$ (両辺を同じ写像で計算するので較正誤りは検出できない) | いいえ |
| `bisim6` | 深さ 6 の双模倣 | いいえ |
| `checkAll` | 区間の全標準行列についての一般定理 | はい (区間全体) |

**印はビルドが計算する。** ✅ は証明書レジストリから、$`f_n`$ は行が指す名前空間を
証明ファイルから探して付ける。名前空間を消したり改名したりすると印そのものが消えるので、
実体の無い印は残らない。

# 値についての注意

**$`\psi_\Omega(Z(1))`$ 以上の行の値は外部資料と食い違っており、まだ決着していない。**
BMS `(0,0)(1,1)(2,2)` の Buchholz 値 $`\psi_0(\psi_2(0))`$ には 3 者が一致するが、
そこから $`\mathfrak{T}(M)`$ へ訳す段で割れる:

```math
\text{当方} \;\longmapsto\; \psi_\Omega(Z(1)) \qquad
\text{資料} \;\longmapsto\; \psi_\Omega(\bar\varphi(1, \Omega+1))
```

**根は型にある** ([D.TM](#dtm))。$`Z(1)`$ は $`\Omega_2`$ ではなく $`I`$ で、
$`\Omega_2 = \chi_0(1)`$ は現在の型では書けない。直すには項型を変える必要がある。

**✅ の付いた行は影響を受けない。** ✅ は [E.cert](#ecert) から来ており、
翻訳関数を一度も通らないからである。

外部の対応表との差分は [diff.md](diff.md) に、再実行手順は
[scripts/external-check.py](../scripts/external-check.py) にある。

# 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean) ·
[証明書](../lean/Evidence/Cert.lean)
