# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.1.47

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

- **証明列**: ✅ = [意味証明書](../lean/Evidence/Cert.lean) `Certified M t`
  (行列の値が t であることの、展開閉包全体を含む閉じた帰納) が Lean に存在する行。
  ビルドが証明書レジストリから機械的に付与し、手で宣言することはできない。
  旧来の「o?-値についての定理」ベースの ✅ は較正事故により撤去した (警告参照)。
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査であり、
  **較正誤りを検出できない**ことが今回実証された):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
  - bisim6 = 深さ 6 の双模倣 (展開列と基本列が一致する領域で有効)。
  - oStageC = Stage C の候補翻訳 oStageC? の値の一致。

## 対応表

| BMS | $`T(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L86) | $`0`$ | $`0`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L88) | $`1`$ | $`1`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L89) | $`2`$ | $`2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L90) | $`\omega`$ | $`\omega`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L92) | $`\omega+\omega`$ | $`\omega\cdot 2`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L94) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L96) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L98) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\varepsilon_0`$ |  | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明 |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L101) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| [`(0,0)(1,1)(0,0)`](../lean/Rows/TM.lean#L103) | $`\bar{\varphi}(1,0)+1`$ | $`\varepsilon_0+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L105) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L107) | $`\bar{\varphi}(1,1)`$ | $`\varepsilon_1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L109) | $`\bar{\varphi}(1,\omega)`$ | $`\varepsilon_\omega`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(0,0)`](../lean/Rows/TM.lean#L111) | $`\bar{\varphi}(1,\omega)+1`$ | $`\varepsilon_\omega+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(2,0)`](../lean/Rows/TM.lean#L113) | $`\bar{\varphi}(1,\bar{\varphi}(0,2))`$ | $`\varepsilon_{\omega^2}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,0)`](../lean/Rows/TM.lean#L115) | $`\bar{\varphi}(1,\bar{\varphi}(0,\omega))`$ | $`\varepsilon_{\omega^\omega}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L118) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\varepsilon_{\varepsilon_0}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L120) | $`\bar{\varphi}(2,0)`$ | $`\zeta_0`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(0,0)`](../lean/Rows/TM.lean#L122) | $`\bar{\varphi}(2,0)+1`$ | $`\zeta_0+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,0)`](../lean/Rows/TM.lean#L124) | $`\bar{\varphi}(0,\bar{\varphi}(2,0))`$ | $`\omega^{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,1)`](../lean/Rows/TM.lean#L126) | $`\bar{\varphi}(1,\bar{\varphi}(2,0))`$ | $`\varepsilon_{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |

## 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)
