# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $T(M)$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。
**機械検査を通った行のみ**を掲載する。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **$o$ 列**: ✅ = 翻訳関数 $o$ がこの行列で定義され $o(M) = t$ が成立 (E1)。
  $o$ の定義域全体ではコーパス検査 (E2 順序埋め込み・E3 相互共終) 済み。
- **その他のエビデンス**: bisim6 = 深さ 6 の双模倣
  (展開列と基本列が一致する領域で有効)。

| BMS | $T(M)$ | 通称 | $o$ | その他のエビデンス | 備考 |
|---|---|---|---|---|---|
| `(空)` | $0$ | $0$ | ✅ | bisim6 | 空行列 |
| `(0)` | $1$ | $1$ | ✅ | bisim6 |  |
| `(0)(0)` | $2$ | $2$ | ✅ | bisim6 |  |
| `(0)(1)` | $\omega$ | $\omega$ | ✅ | bisim6 |  |
| `(0)(1)(0)(1)` | $\omega+\omega$ | $\omega\cdot 2$ | ✅ | bisim6 |  |
| `(0)(1)(1)` | $\bar{\varphi}(0,2)$ | $\omega^2$ | ✅ | bisim6 |  |
| `(0)(1)(2)` | $\bar{\varphi}(0,\omega)$ | $\omega^\omega$ | ✅ | bisim6 |  |
| `(0)(1)(2)(3)` | $\bar{\varphi}(0,\bar{\varphi}(0,\omega))$ | $\omega^{\omega^\omega}$ | ✅ | bisim6 |  |
| `(0,0)(1,1)` | $\bar{\varphi}(1,0)$ | $\varepsilon_0$ |  | bisim6 | 2 行の最初の極限 |
| `(0,0)(1,1)(1,0)` | $\bar{\varphi}(0,\bar{\varphi}(1,0))$ | $\omega^{\varepsilon_0+1}$ |  | bisim6 |  |
