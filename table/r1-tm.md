# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.1.21

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。
**機械検査を通った行のみ**を掲載する。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **証明列**: ✅ = その行の主張が **任意の $`n`$ について** Lean で証明済み
  (リンク先がその証明)。極限行は E3: 1 行領域では等式
  $`\forall n.\ o(M[n]) = t[n{+}1]`$、Stage B 以降では展開値の閉形式と
  相互共終 (両列が互いに追い越し合う witness 付き)。
  後続行は $`\forall n.\ o(M[n]) = t-1`$、零行は $`o(M) = t`$。
  表で唯一、検査ではなく証明である列。
- **太字の区間行**: 個別の行列ではなく**区間内の全標準行列**への主張。
  ✅ が付けば区間まるごと一般定理で証明済み (それまでは弱いエビデンスのみ)。
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
    $`o`$ の定義域全体では [コーパス検査](../lean/Evidence/Check.lean)
    (E2 順序埋め込み・E3 相互共終) 済み。
  - bisim6 = 深さ 6 の双模倣 (展開列と基本列が一致する領域で有効)。
  - oStageC = Stage C の候補翻訳 oStageC? の値の一致。コーパス検査済みだが、
    上位領域に未解決の設計問題が残るため $`o`$ への統合は保留中。

## 対応表

| BMS | $`T(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L84) | $`0`$ | $`0`$ | [✅](../lean/Rows/Proofs.lean#L42) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L86) | $`1`$ | $`1`$ | [✅](../lean/Rows/Proofs.lean#L55) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L87) | $`2`$ | $`2`$ | [✅](../lean/Rows/Proofs.lean#L68) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L88) | $`\omega`$ | $`\omega`$ | [✅](../lean/Rows/Proofs.lean#L81) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L90) | $`\omega+\omega`$ | $`\omega\cdot 2`$ | [✅](../lean/Rows/Proofs.lean#L94) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L92) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ | [✅](../lean/Rows/Proofs.lean#L107) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L94) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ | [✅](../lean/Rows/Proofs.lean#L120) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L96) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ | [✅](../lean/Rows/Proofs.lean#L133) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\varepsilon_0`$ | [✅](../lean/Evidence/StageA.lean#L1409) | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明 |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L99) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ | [✅](../lean/Rows/ProofsB.lean#L775) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L101) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ | [✅](../lean/Rows/ProofsB.lean#L1747) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L103) | $`\bar{\varphi}(1,1)`$ | $`\varepsilon_1`$ | [✅](../lean/Rows/ProofsB.lean#L1954) | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L105) | $`\bar{\varphi}(1,\omega)`$ | $`\varepsilon_\omega`$ | [✅](../lean/Rows/ProofsB.lean#L1472) | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L107) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\varepsilon_{\varepsilon_0}`$ | [✅](../lean/Rows/ProofsB.lean#L980) | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L109) | $`\bar{\varphi}(2,0)`$ | $`\zeta_0`$ | [✅](../lean/Rows/ProofsB.lean#L498) | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L111) | $`\bar{\varphi}(2,1)`$ | $`\zeta_1`$ | [✅](../lean/Rows/ProofsB.lean#L2309) | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,0)`](../lean/Rows/TM.lean#L113) | $`\bar{\varphi}(2,\omega)`$ | $`\zeta_\omega`$ | [✅](../lean/Rows/ProofsB.lean#L1561) | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L115) | $`\bar{\varphi}(3,0)`$ | $`\bar{\varphi}(3,0)`$ | [✅](../lean/Rows/ProofsB.lean#L621) | [o](../lean/Trans/TM.lean) |  |
| **(0,0)(1,1)…(a,1), a≥1** | $`\bar{\varphi}(a,0)`$ | $`\varepsilon_0,\ \zeta_0,\ \bar{\varphi}(3,0),\ldots`$ | [✅](../lean/Evidence/StageB.lean#L1095) |  | 1 パラメータ族 (対角線) の一括証明。a=1,2,3 が表の ε₀, ζ₀, φ̄(3,0) 行、族の sup が φ̄(ω,0) |
| **(0,0)(1,1)…(a,1)(a,1), a≥1** | $`\bar{\varphi}(a,1)`$ | $`\varepsilon_1,\ \zeta_1,\ \bar{\varphi}(3,1),\ldots`$ | [✅](../lean/Evidence/StageB.lean#L2032) |  | 1 パラメータ族の一括証明。a=1,2 の ε₁, ζ₁ 行は定理としてインスタンス化 |
| **(0,0)(1,1)…(a,1)(a+1,0), a≥1** | $`\bar{\varphi}(a,\omega)`$ | $`\varepsilon_\omega,\ \zeta_\omega,\ \bar{\varphi}(3,\omega),\ldots`$ | [✅](../lean/Evidence/StageB.lean#L531) |  | 1 パラメータ族の一括証明。a=1,2 が表の ε_ω, ζ_ω 行、a≥3 は表の先へ無限に続く |
| [`(0,0)(1,1)(2,2)`](../lean/Rows/TM.lean#L117) | $`\bar{\varphi}(\omega,0)`$ | $`\bar{\varphi}(\omega,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 行 1 に 2 が現れる最初の行 |
| [`(0,0)(1,1)(2,2)(1,1)`](../lean/Rows/TM.lean#L120) | $`\bar{\varphi}(1,\bar{\varphi}(\omega,0))`$ | $`\varepsilon_{\bar{\varphi}(\omega,0)+1}`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)`](../lean/Rows/TM.lean#L122) | $`\bar{\varphi}(2,\bar{\varphi}(\omega,0))`$ | $`\bar{\varphi}(2,\bar{\varphi}(\omega,0)+1)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,2)`](../lean/Rows/TM.lean#L124) | $`\bar{\varphi}(\omega,1)`$ | $`\bar{\varphi}(\omega,1)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,2)`](../lean/Rows/TM.lean#L126) | $`\bar{\varphi}(\omega,\omega)`$ | $`\bar{\varphi}(\omega,\omega)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,2)(2,2)`](../lean/Rows/TM.lean#L128) | $`\bar{\varphi}(\omega,\bar{\varphi}(0,2))`$ | $`\bar{\varphi}(\omega,\omega^2)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)`](../lean/Rows/TM.lean#L130) | $`\bar{\varphi}(\omega,\bar{\varphi}(0,\omega))`$ | $`\bar{\varphi}(\omega,\omega^\omega)`$ |  | [oStageC](../lean/Trans/StageC.lean) | v0.1.10 の値を訂正 ((2,2) 反復列の sup) |
| [`(0,0)(1,1)(2,2)(3,0)(3,0)`](../lean/Rows/TM.lean#L133) | $`\bar{\varphi}(\omega,\bar{\varphi}(0,\omega+1))`$ | $`\bar{\varphi}(\omega,\omega^{\omega+1})`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,0)`](../lean/Rows/TM.lean#L135) | $`\bar{\varphi}(\omega,\bar{\varphi}(0,\omega+\omega))`$ | $`\bar{\varphi}(\omega,\omega^{\omega\cdot 2})`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)`](../lean/Rows/TM.lean#L137) | $`\bar{\varphi}(\omega,\bar{\varphi}(0,\bar{\varphi}(0,2)))`$ | $`\bar{\varphi}(\omega,\omega^{\omega^2})`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(3,1)`](../lean/Rows/TM.lean#L139) | $`\bar{\varphi}(\omega+1,0)`$ | $`\bar{\varphi}(\omega+1,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(3,2)`](../lean/Rows/TM.lean#L141) | $`\bar{\varphi}(\bar{\varphi}(0,2),0)`$ | $`\bar{\varphi}(\omega^2,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |

## 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)
