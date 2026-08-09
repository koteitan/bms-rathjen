# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.1.41

> **⚠ 警告 (v0.1.41)**: 本表の翻訳 $`o`$ に系統的な較正誤りが発見されたため、
> **証明列 (✅) を全行から一時撤去した**。BMS 順で `(0,0)(1,1)(2,1)(2,0)` 以上の行の
> $`T(M)`$ 値と通称は**誤っている**
> (例: 真の値は $`(0,0)(1,1)(2,1)(2,0) = \zeta_\omega`$、
> $`(0,0)(1,1)(2,1)(3,1) = \Gamma_0`$、$`(0,0)(1,1)(2,2) = \psi_0(\Omega_2)`$ —
> P進大好きbot 氏のペア数列停止性証明の変換写像による)。
> それ未満の行は変換写像と一致することを確認済み。表は再構築中。

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **証明列**: 一時撤去中 (上記警告を参照)。従来の ✅ は「o?-値についての
  Lean 定理」を意味していたが、o? 自身の較正誤りにより行の意味論
  (行列の順序数 = 表記の値) は保証されないことが判明した。
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査であり、
  **較正誤りを検出できない**ことが今回実証された):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
  - bisim6 = 深さ 6 の双模倣 (展開列と基本列が一致する領域で有効)。
  - oStageC = Stage C の候補翻訳 oStageC? の値の一致。

## 対応表

| BMS | $`T(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L84) | $`0`$ | $`0`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L86) | $`1`$ | $`1`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L87) | $`2`$ | $`2`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L88) | $`\omega`$ | $`\omega`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L90) | $`\omega+\omega`$ | $`\omega\cdot 2`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L92) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L94) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L96) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\varepsilon_0`$ |  | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明 |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L99) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| [`(0,0)(1,1)(0,0)`](../lean/Rows/TM.lean#L101) | $`\bar{\varphi}(1,0)+1`$ | $`\varepsilon_0+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L103) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L105) | $`\bar{\varphi}(1,1)`$ | $`\varepsilon_1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L107) | $`\bar{\varphi}(1,\omega)`$ | $`\varepsilon_\omega`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(0,0)`](../lean/Rows/TM.lean#L109) | $`\bar{\varphi}(1,\omega)+1`$ | $`\varepsilon_\omega+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(2,0)`](../lean/Rows/TM.lean#L111) | $`\bar{\varphi}(1,\bar{\varphi}(0,2))`$ | $`\varepsilon_{\omega^2}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,0)`](../lean/Rows/TM.lean#L113) | $`\bar{\varphi}(1,\bar{\varphi}(0,\omega))`$ | $`\varepsilon_{\omega^\omega}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L116) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\varepsilon_{\varepsilon_0}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L118) | $`\bar{\varphi}(2,0)`$ | $`\zeta_0`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(0,0)`](../lean/Rows/TM.lean#L120) | $`\bar{\varphi}(2,0)+1`$ | $`\zeta_0+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,0)`](../lean/Rows/TM.lean#L122) | $`\bar{\varphi}(0,\bar{\varphi}(2,0))`$ | $`\omega^{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,1)`](../lean/Rows/TM.lean#L124) | $`\bar{\varphi}(1,\bar{\varphi}(2,0))`$ | $`\varepsilon_{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(2,0)`](../lean/Rows/TM.lean#L126) | $`\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(2,0)))`$ | $`\varepsilon_{\zeta_0\cdot\omega}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L129) | $`\bar{\varphi}(2,1)`$ | $`\zeta_1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,0)`](../lean/Rows/TM.lean#L131) | $`\bar{\varphi}(2,\omega)`$ | $`\zeta_\omega`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,0)(4,1)`](../lean/Rows/TM.lean#L133) | $`\bar{\varphi}(2,\bar{\varphi}(1,0))`$ | $`\zeta_{\varepsilon_0}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L136) | $`\bar{\varphi}(3,0)`$ | $`\bar{\varphi}(3,0)`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,1)(0,0)`](../lean/Rows/TM.lean#L138) | $`\bar{\varphi}(3,0)+1`$ | $`\bar{\varphi}(3,0)+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,1)(1,0)`](../lean/Rows/TM.lean#L140) | $`\bar{\varphi}(0,\bar{\varphi}(3,0))`$ | $`\omega^{\bar{\varphi}(3,0)+1}`$ |  | [o](../lean/Trans/TM.lean) |  |
| **(0,0)(1,1)…(a,1)(b,r), a≥1, b≤a+1, (b,r)≠(0,1)** | 下の 7 行の場合分け |  |  |  | 傘: 梯子+1列の全行列で o? が定義され 7 分岐の値に一致 (E1 を全ての a で証明)。E3 は下の各族行の形で成立 |
| **(0,0)(1,1)…(a,1), a≥1** | $`\bar{\varphi}(a,0)`$ | $`\varepsilon_0,\ \zeta_0,\ \bar{\varphi}(3,0),\ldots`$ |  |  | 1 パラメータ族 (対角線) の一括証明。a=1,2,3 が表の ε₀, ζ₀, φ̄(3,0) 行、族の sup が φ̄(ω,0) |
| **(0,0)(1,1)…(a,1)(0,0), a≥1** | $`\bar{\varphi}(a,0)+1`$ | $`\varepsilon_0+1,\ \zeta_0+1,\ldots`$ |  |  | 後続行の 1 パラメータ族 (E1 と後続則を全ての a で証明) |
| **(0,0)(1,1)…(a,1)(1,0), a≥1** | $`\bar{\varphi}(0,\bar{\varphi}(a,0))`$ | $`\omega^{\varepsilon_0+1},\ \omega^{\zeta_0+1},\ldots`$ |  |  | 1 パラメータ族の一括証明。a=1 が表の ω^(ε₀+1) 行 |
| **(0,0)(1,1)…(a,1)(b,0), 2≤b≤a** | $`\bar{\varphi}(b{-}1,\bar{\varphi}(0,\bar{\varphi}(a,0)))`$ | $`\varepsilon_{\zeta_0\cdot\omega},\ldots`$ |  |  | 2 パラメータ族の一括証明。これで梯子+1列 (r=0) の全ケースが証明済み |
| **(0,0)(1,1)…(a,1)(b,1), 1≤b<a** | $`\bar{\varphi}(b,\bar{\varphi}(a,0))`$ | $`\varepsilon_{\zeta_0+1},\ldots`$ |  |  | 2 パラメータ族の一括証明。これで梯子+1列の全 7 ケース (F4) が完全証明 |
| **(0,0)(1,1)…(a,1)(a,1), a≥1** | $`\bar{\varphi}(a,1)`$ | $`\varepsilon_1,\ \zeta_1,\ \bar{\varphi}(3,1),\ldots`$ |  |  | 1 パラメータ族の一括証明。a=1,2 の ε₁, ζ₁ 行は定理としてインスタンス化 |
| **(0,0)(1,1)…(a,1)(a+1,0), a≥1** | $`\bar{\varphi}(a,\omega)`$ | $`\varepsilon_\omega,\ \zeta_\omega,\ \bar{\varphi}(3,\omega),\ldots`$ |  |  | 1 パラメータ族の一括証明。a=1,2 が表の ε_ω, ζ_ω 行、a≥3 は表の先へ無限に続く |
| **(0,0)(1,1)…(a,1)(a+1,0)(a+1,0), a≥1** | $`\bar{\varphi}(a,\omega^2)`$ | $`\varepsilon_{\omega^2},\ \zeta_{\omega^2},\ldots`$ |  |  | 梯子+2列族。a=1 が表の ε_{ω²} 行 |
| **(0,0)(1,1)…(a,1)(a+1,0)(a+2,0), a≥1** | $`\bar{\varphi}(a,\omega^\omega)`$ | $`\varepsilon_{\omega^\omega},\ \zeta_{\omega^\omega},\ldots`$ |  |  | 梯子+2列族。a=1 が表の ε_{ω^ω} 行 |
| **(0,0)(1,1)…(a,1)(a+1,0)(a+2,1), a≥1** | $`\bar{\varphi}(a,\varepsilon_0)`$ | $`\varepsilon_{\varepsilon_0},\ \zeta_{\varepsilon_0},\ldots`$ |  |  | 初の梯子+2列族。a=1 が表の ε_{ε₀} 行 (R5 の手証明は族定理のインスタンスに退役) |
| [`(0,0)(1,1)(2,2)`](../lean/Rows/TM.lean#L143) | $`\bar{\varphi}(\omega,0)`$ | $`\bar{\varphi}(\omega,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 行 1 に 2 が現れる最初の行 |
| [`(0,0)(1,1)(2,2)(1,1)`](../lean/Rows/TM.lean#L146) | $`\bar{\varphi}(1,\bar{\varphi}(\omega,0))`$ | $`\varepsilon_{\bar{\varphi}(\omega,0)+1}`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)`](../lean/Rows/TM.lean#L153) | $`\bar{\varphi}(2,\bar{\varphi}(\omega,0))`$ | $`\bar{\varphi}(2,\bar{\varphi}(\omega,0)+1)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L155) | $`\bar{\varphi}(3,\bar{\varphi}(\omega,0))`$ | $`\bar{\varphi}(3,\bar{\varphi}(\omega,0)+1)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L157) | $`\bar{\varphi}(\omega,1)`$ | $`\bar{\varphi}(\omega,1)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L159) | $`\bar{\varphi}(\omega,2)`$ | $`\bar{\varphi}(\omega,2)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)`](../lean/Rows/TM.lean#L161) | $`\bar{\varphi}(\omega,\omega)`$ | $`\bar{\varphi}(\omega,\omega)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(2,0)`](../lean/Rows/TM.lean#L163) | $`\bar{\varphi}(\omega,\bar{\varphi}(0,2))`$ | $`\bar{\varphi}(\omega,\omega^2)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,0)`](../lean/Rows/TM.lean#L165) | $`\bar{\varphi}(\omega,\bar{\varphi}(0,\omega))`$ | $`\bar{\varphi}(\omega,\omega^\omega)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)`](../lean/Rows/TM.lean#L167) | $`\bar{\varphi}(\omega,\bar{\varphi}(1,0))`$ | $`\bar{\varphi}(\omega,\varepsilon_0)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)(4,2)`](../lean/Rows/TM.lean#L169) | $`\bar{\varphi}(\omega,\bar{\varphi}(\omega,0))`$ | $`\bar{\varphi}(\omega,\bar{\varphi}(\omega,0))`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)`](../lean/Rows/TM.lean#L171) | $`\bar{\varphi}(\omega+1,0)`$ | $`\bar{\varphi}(\omega+1,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 旧候補値を訂正 (v0.1.35) |
| [`(0,0)(1,1)(2,2)(2,1)(2,1)`](../lean/Rows/TM.lean#L174) | $`\bar{\varphi}(\omega+1,1)`$ | $`\bar{\varphi}(\omega+1,1)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,1)`](../lean/Rows/TM.lean#L176) | $`\bar{\varphi}(\omega+2,0)`$ | $`\bar{\varphi}(\omega+2,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,2)`](../lean/Rows/TM.lean#L178) | $`\bar{\varphi}(\omega+\omega,0)`$ | $`\bar{\varphi}(\omega\cdot 2,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 旧候補値を訂正 (v0.1.35) |
| [`(0,0)(1,1)(2,2)(2,2)`](../lean/Rows/TM.lean#L181) | $`\bar{\varphi}(\bar{\varphi}(0,2),0)`$ | $`\bar{\varphi}(\omega^2,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 旧候補値を訂正 (v0.1.35) |
| [`(0,0)(1,1)(2,2)(2,2)(2,2)`](../lean/Rows/TM.lean#L184) | $`\bar{\varphi}(\bar{\varphi}(0,3),0)`$ | $`\bar{\varphi}(\omega^3,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 旧候補値を訂正 (v0.1.35) |
| [`(0,0)(1,1)(2,2)(3,0)`](../lean/Rows/TM.lean#L187) | $`\bar{\varphi}(\bar{\varphi}(0,\omega),0)`$ | $`\bar{\varphi}(\omega^\omega,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 旧候補値を 2 度訂正 (v0.1.11, v0.1.35) |
| [`(0,0)(1,1)(2,2)(3,0)(3,0)`](../lean/Rows/TM.lean#L190) | $`\bar{\varphi}(\bar{\varphi}(0,\bar{\varphi}(0,2)),0)`$ | $`\bar{\varphi}(\omega^{\omega^2},0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 旧候補値を訂正 (v0.1.35) |
| [`(0,0)(1,1)(2,2)(3,0)(4,0)`](../lean/Rows/TM.lean#L193) | $`\bar{\varphi}(\bar{\varphi}(0,\bar{\varphi}(0,\omega)),0)`$ | $`\bar{\varphi}(\omega^{\omega^\omega},0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 旧候補値を訂正 (v0.1.35) |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)`](../lean/Rows/TM.lean#L196) | $`\bar{\varphi}(\bar{\varphi}(1,0),0)`$ | $`\bar{\varphi}(\varepsilon_0,0)`$ |  | [oStageC](../lean/Trans/StageC.lean) | 旧候補値を訂正 (v0.1.35) |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)`](../lean/Rows/TM.lean#L199) | $`\bar{\varphi}(\bar{\varphi}(\omega,0),0)`$ | $`\bar{\varphi}(\bar{\varphi}(\omega,0),0)`$ |  | [oStageC](../lean/Trans/StageC.lean) |  |
| [`(0,0)(1,1)(2,2)(3,1)`](../lean/Rows/TM.lean#L201) | $`\psi_{\Omega}(0)`$ | $`\Gamma_0`$ |  | [oStageC](../lean/Trans/StageC.lean) | ψ 項の初登場: Γ₀ = ψ_Ω(0)。展開連鎖は Γ-塔 W, φ̄(W,0), … (旧候補値を訂正) |

## 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)
