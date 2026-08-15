# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.7.38

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`\mathfrak{T}(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応。

**証明列の ✅ は[証明の仕様](#証明の仕様)の E.cert が Lean の定理であることを意味する。**
それ以外の印は ✅ の材料であって ✅ ではない。**印はすべてビルドが計算して付ける**
(手で書けない)。

- 作り方・作業手順・資料の場所 — [plan/README.md](../plan/README.md)
- 表を読むとき・書くときの原則 (注意書き) — [plan/constitutions.md](../plan/constitutions.md)
- この表自身の仕様 — [plan/spec.md](../plan/spec.md)
- 外部の対応表との差分 — [diff.md](diff.md)
- 本筋から外した補足 — [misc.md](misc.md)

## 列の意味

| 列 | 中身 |
|---|---|
| BMS | 行列。リンク先は行の定義 |
| $`\mathfrak{T}(M)`$ | Rathjen R1 の項 ([D.TM](#dtm)) |
| Buchholz | Buchholz の $`\mathrm{OT}_B`$ での値。$`\psi_0(\Omega_2)`$ 以上は変換写像 (pss2bp) の出力そのもの、それ未満は通称 |
| 証明 | ✅ = [E.cert](#ecert) が定理。空欄 = まだ |
| その他の弱いエビデンス | ✅ の材料。[一覧](#その他の弱いエビデンス) |
| 備考 | その行に固有のこと |

## 対応表

| BMS | $`\mathfrak{T}(M)`$ | Buchholz | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
