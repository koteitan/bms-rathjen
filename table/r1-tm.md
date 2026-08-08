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
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
    $`o`$ の定義域全体では [コーパス検査](../lean/Evidence/Check.lean)
    (E2 順序埋め込み・E3 相互共終) 済み。
  - bisim6 = 深さ 6 の双模倣 (展開列と基本列が一致する領域で有効)。

## 対応表

| BMS | $`T(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L78) | $`0`$ | $`0`$ | [✅](../lean/Rows/Proofs.lean#L206) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L80) | $`1`$ | $`1`$ | [✅](../lean/Rows/Proofs.lean#L219) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L81) | $`2`$ | $`2`$ | [✅](../lean/Rows/Proofs.lean#L233) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L82) | $`\omega`$ | $`\omega`$ | [✅](../lean/Rows/Proofs.lean#L246) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L84) | $`\omega+\omega`$ | $`\omega\cdot 2`$ | [✅](../lean/Rows/Proofs.lean#L272) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L86) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ | [✅](../lean/Rows/Proofs.lean#L309) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L88) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ | [✅](../lean/Rows/Proofs.lean#L380) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L90) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ | [✅](../lean/Rows/Proofs.lean#L418) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L93) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ |  | [bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限。$`o`$ 未定義のため証明は Stage B 待ち |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L95) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ |  | [bisim6](../lean/Evidence/Bisim.lean) |  |

## 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)
