# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。
**機械検査を通った行のみ**を掲載する。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **証明列**: ✅ = その行の主張が **任意の $`n`$ について** Lean で証明済み
  (リンク先がその証明)。極限行は E3 $`\forall n.\ o(M[n]) = t[n{+}1]`$、
  後続行は $`\forall n.\ o(M[n]) = t-1`$、零行は $`o(M) = t`$。
  表で唯一、検査ではなく証明である列。
- **太字の区間行**: 個別の行列ではなく**区間内の全標準行列**への主張。
  ✅ が付けば区間まるごと一般定理で証明済み (それまでは弱いエビデンスのみ)。
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
    $`o`$ の定義域全体では [コーパス検査](../lean/Evidence/Check.lean)
    (E2 順序埋め込み・E3 相互共終) 済み。
  - bisim6 = 深さ 6 の双模倣 (展開列と基本列が一致する領域で有効)。

## 対応表

| BMS | $`T(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L79) | $`0`$ | $`0`$ | [✅](../lean/Rows/Proofs.lean#L42) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L81) | $`1`$ | $`1`$ | [✅](../lean/Rows/Proofs.lean#L55) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L82) | $`2`$ | $`2`$ | [✅](../lean/Rows/Proofs.lean#L68) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L83) | $`\omega`$ | $`\omega`$ | [✅](../lean/Rows/Proofs.lean#L81) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L85) | $`\omega+\omega`$ | $`\omega\cdot 2`$ | [✅](../lean/Rows/Proofs.lean#L94) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L87) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ | [✅](../lean/Rows/Proofs.lean#L107) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L89) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ | [✅](../lean/Rows/Proofs.lean#L120) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L91) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ | [✅](../lean/Rows/Proofs.lean#L133) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\varepsilon_0`$ | [✅](../lean/Evidence/StageA.lean#L1409) | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明 |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L94) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L96) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L98) | $`\bar{\varphi}(1,1)`$ | $`\varepsilon_1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L99) | $`\bar{\varphi}(1,\omega)`$ | $`\varepsilon_\omega`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L101) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\varepsilon_{\varepsilon_0}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L103) | $`\bar{\varphi}(2,0)`$ | $`\zeta_0`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L104) | $`\bar{\varphi}(2,1)`$ | $`\zeta_1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,0)`](../lean/Rows/TM.lean#L106) | $`\bar{\varphi}(2,\omega)`$ | $`\zeta_\omega`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L108) | $`\bar{\varphi}(3,0)`$ | $`\bar{\varphi}(3,0)`$ |  | [o](../lean/Trans/TM.lean) |  |

## 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)
