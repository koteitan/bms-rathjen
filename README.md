# pss-rathjen

順序数表記と見做した BMS (Bashicu Matrix System) と、Rathjen の順序数崩壊関数の
対応表を、Lean による機械検証付きで作るプロジェクト。

- **[対応表 (R1: BMS × T(M))](table/r1-tm.md)** — 機械検査を通った行のみ掲載
- [計画とエビデンスの設計](plan/README.md) — 何を証明することをエビデンスとするか (E1/E2/E3/G/MT)
- [Rathjen の表記系一覧 (強さ順)](rathjen-ordinals.md) — R1〜R5 と最終ターゲット

## 構成

- `lean/` — Lean 4 (v4.30.0, 外部依存なし) による形式化
  - `BMS/` BM4 の行列・辞書式順序・展開・標準形
    ([yaBMS](https://github.com/koteitan/yaBMS) の C 実装との突き合わせ済み)
  - `TM/` Rathjen 𝔗(M) の項・順序・正規形 (Rathjen 1991 §2 に忠実)・基本列
  - `Trans/` 翻訳関数 o (小さい領域から段階的に拡張中)
  - `Evidence/` 検査器 (順序埋め込み・相互共終・双模倣)
  - `Rows/` 対応表の行データベースと行ごとの機械検査
- `table/` — 生成物 (手編集しない)
- `scripts/crosscheck.sh` — yaBMS との出力照合

## 検証と再生成

```sh
cd lean && lake build                      # 全行の検査 (#guard) を含む
lake exe gentable > ../table/r1-tm.md      # 表の再生成
YABMS=/path/to/yaBMS/c/bms ../scripts/crosscheck.sh   # BMS 実装の照合
```
