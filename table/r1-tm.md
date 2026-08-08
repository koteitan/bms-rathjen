# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。
**機械検査を通った行のみ**を掲載する。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **$`o`$ 列**: ✅ = 翻訳関数 $`o`$ ([定義](../lean/Trans/TM.lean)) がこの行列で定義され
  $`o(M) = t`$ が成立 (E1)。$`o`$ の定義域全体では
  [コーパス検査](../lean/Evidence/Check.lean) (E2 順序埋め込み・E3 相互共終) 済み。
- **その他の弱いエビデンス**: [bisim6](../lean/Evidence/Bisim.lean) = 深さ 6 の双模倣
  (展開列と基本列が一致する領域で有効)。

実装:
[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)

| BMS | $`T(M)`$ | 通称 | $`o`$ | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
| `(空)` | $`0`$ | $`0`$ | [✅](../lean/Trans/TM.lean) | [bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| `(0)` | $`1`$ | $`1`$ | [✅](../lean/Trans/TM.lean) | [bisim6](../lean/Evidence/Bisim.lean) |  |
| `(0)(0)` | $`2`$ | $`2`$ | [✅](../lean/Trans/TM.lean) | [bisim6](../lean/Evidence/Bisim.lean) |  |
| `(0)(1)` | $`\omega`$ | $`\omega`$ | [✅](../lean/Trans/TM.lean) | [bisim6](../lean/Evidence/Bisim.lean) |  |
| `(0)(1)(0)(1)` | $`\omega+\omega`$ | $`\omega\cdot 2`$ | [✅](../lean/Trans/TM.lean) | [bisim6](../lean/Evidence/Bisim.lean) |  |
| `(0)(1)(1)` | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ | [✅](../lean/Trans/TM.lean) | [bisim6](../lean/Evidence/Bisim.lean) |  |
| `(0)(1)(2)` | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ | [✅](../lean/Trans/TM.lean) | [bisim6](../lean/Evidence/Bisim.lean) |  |
| `(0)(1)(2)(3)` | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ | [✅](../lean/Trans/TM.lean) | [bisim6](../lean/Evidence/Bisim.lean) |  |
| `(0,0)(1,1)` | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ |  | [bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| `(0,0)(1,1)(1,0)` | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ |  | [bisim6](../lean/Evidence/Bisim.lean) |  |
