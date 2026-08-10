# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.2.1

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

対応表の各行 $`(M, t)`$ について、レジストリ
$`\mathrm{certRows}`$ に登録された行が満たす命題。名前は Lean の識別子で、
`E.` は表の主張を支える定理、`P.` はその補助命題、`D.` は定義。実装は
[`lean/Evidence/Cert.lean`](../lean/Evidence/Cert.lean)。

- [E.certIn_rows_inT — 登録の条件 (ゲート)](#ecertin_rows_int--登録の条件-ゲート)
- [E.certRows_unique_gate — 一意性](#ecertrows_unique_gate--一意性)
- [E.certRows_no_overshoot — 上限 (無条件)](#ecertrows_no_overshoot--上限-無条件)
- [E.no_cert_above_eps0 — ε₀ 行の鋭い上限](#eno_cert_above_eps0--ε₀-行の鋭い上限)
- [まだ排除できていないこと](#まだ排除できていないこと)
- [その他の弱いエビデンス](#その他の弱いエビデンス)
- [定義](#定義): [D.Certified](#dcertified--行列が項を表すこと) ·
  [D.CertifiedIn / D.DomI](#dcertifiedin--ddomi--値の側を-tm-に閉じ込めたもの) ·
  [D.certRows](#dcertrows--レジストリ)

## E.certIn_rows_inT — 登録の条件 (ゲート)

```math
\forall (M,t) \in \mathrm{certRows}.\;\; \mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;t
```

登録されたすべての行が、**導出に現れる値がすべて $`\mathfrak{T}(M)`$ の項である**
証明書を持つ。これがレジストリのゲートであり、これを満たさない行は登録できない。
$`\mathrm{certRows}`$ を拡張してこの証明を拡張しなければビルドが壊れる。

証明列 ✅ はこのゲートから機械的に付与されるもので、手で書くことはできない。

## E.certRows_unique_gate — 一意性

```math
\forall (M,t) \in \mathrm{certRows}.\;\forall u.\;\;
\mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;u \;\Longrightarrow\; u = t
```

ゲートが要求する範囲の証明書 — 値が遺伝的に $`\mathfrak{T}(M)`$ の項であるもの —
では、**登録値以外の値は取り得ない**。上下いずれの側も排除されている。
登録の条件 (E.certIn_rows_inT) と一意性の条件が**同じ $`\mathrm{DomI}`$**
であることに注意。

## E.certRows_no_overshoot — 上限 (無条件)

```math
\forall (M,t) \in \mathrm{certRows}.\;\forall u.\;\;
\mathrm{Certified}\;M\;u \;\Longrightarrow\; \bar\varphi(0,\,t+1) \not\le u
```

値が $`\mathfrak{T}(M)`$ の外に出るものも含め、**いかなる**証明書も
$`\bar\varphi(0, t+1) = \omega^{t+1}`$ 以上の値を与えない。
$`\mathrm{DomI}`$ の仮定が無いことに注意 — これは無条件である。

## E.no_cert_above_eps0 — ε₀ 行の鋭い上限

```math
\forall u.\;\; \varepsilon_0 < u \;\Longrightarrow\;
\neg\,\mathrm{Certified}\;[(0,0)(1,1)]\;u
```

ε₀ の行では、**ε₀ より上の値は一切認証され得ない**。E.certRows_no_overshoot が
$`\omega^{t+1}`$ 以上を塞ぐのに対し、この行では $`t`$ の直上から塞がれている。

## まだ排除できていないこと

登録値より**下**の値が、$`\mathfrak{T}(M)`$ の外へ出る部分値を経由して
認証される可能性 (ゲートを通らない証明書):

```math
\exists u.\;\; u < t \;\wedge\; \mathrm{Certified}\;M\;u
\;\wedge\; \neg\,\mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;u \;\;?
```

上側は E.certRows_no_overshoot により無条件に塞がっているので、**残る穴は片側のみ**。

P.undershoot_reduction により、この穴は葉 1 枚に還元済み:

> **P.T** $`a \le b \;\to\; b \le c \;\to\; a \le c`$ — 中間項 $`b`$ が
> $`\mathrm{Frag2}`$、**両端点は任意**

P.T は**真だが、このリポジトリの手法では証明できない**。真であること: 7 構成子に
わたる 1010 項の掃引で反例 0、結論を反転した陽性対照は 3628 万回発火する。
証明できないこと: 辞書式帰納法が両端点の第 1 引数の比較可能性を消費するが、それは
$`\mathrm{Frag2}`$ の外で偽である (P.frag2_stops_at_psi)。端点に $`\mathrm{inT}`$
を課せば証明できるが、**開いている場合は $`\mathrm{inT}`$ でない場合**なので
適用できない。

## その他の弱いエビデンス

いずれも有限個の $`n`$ の計算検査であり、**較正誤りを検出できない**ことが
実証されている。表の主張ではなく候補ティアである。

| 記号 | 意味 |
|---|---|
| `o` | 翻訳関数がこの行列で定義され $`o(M) = t`$ |
| `oR` | オラクル較正済みの候補値 (P進大好きbot 氏の変換写像の Lean 移植)。全行一致をビルド時 `#guard` で強制 |
| `bisim6` | 深さ 6 の双模倣 |
| `oStageC` | Stage C の候補翻訳の値の一致 |

# 定義

## D.Certified — 行列が項を表すこと

$`\mathrm{Certified}\;M\;t`$ は「行列 $`M`$ が項 $`t`$ を表す」ことを、
外部の意味論を使わず**展開の再帰だけ**で述べた帰納的述語。導入規則は 3 つ:

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

帰納型なので、$`\mathrm{Certified}\;M\;t`$ を持つとは
**$`M`$ の展開木を根から降りて $`[\,]`$ / $`0`$ に至る導出が実在する**ということ。
整礎性は前提していない。

極限規則の 5 前提のうち**同一性を述べるのは
$`\forall n.\;\mathrm{Certified}\;(M[n])\;(f_n)`$ の 1 つだけ**で、
残る 4 つは列 $`f`$ の性質である。**性質をいくつ検査しても値は決まらない**
([plan/constitutions.md](../plan/constitutions.md) C2)。較正事故はここを
取り違えて起きた。$`f`$ は**パラメータ**であって、特定の基本列に合わせる必要はない。

## D.CertifiedIn / D.DomI — 値の側を $`\mathfrak{T}(M)`$ に閉じ込めたもの

```math
\mathrm{DomI}(t) \;:\equiv\; t \in \mathfrak{T}(M)
```

$`\mathrm{Certified}`$ は認証される値に制約を課さないので、生の項の上では
$`\mathfrak{T}(M)`$ の項でない値も認証されうる。実例 (P.cert_not_single_valued):

```math
\mathrm{Certified}\;[(0)(1)]\;\omega
\qquad\text{かつ}\qquad
\mathrm{Certified}\;[(0)(1)]\;(1+M)
```

$`\mathrm{CertifiedIn}\;\mathrm{Dom}`$ は**導出に現れる値すべて**が
$`\mathrm{Dom}`$ に属することを要求する版。ゲート (E.certIn_rows_inT) が
$`\mathrm{DomI}`$ を要求するのは、この一価性の破れを塞ぐためである。

## D.certRows — レジストリ

登録された $`(M, t)`$ の対のリスト。**✅ はこのリストへの登録から機械的に付与される**。
E.certIn_rows_inT がその登録条件であり、リストを伸ばすには証明を伸ばすしかない。

# 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean) ·
[証明書](../lean/Evidence/Cert.lean)
