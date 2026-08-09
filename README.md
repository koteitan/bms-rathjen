# bms-rathjen

順序数表記と見做した BMS (Bashicu Matrix System) と、Rathjen の順序数崩壊関数の
対応表を、Lean による機械検証付きで作るプロジェクト。

- **[対応表 (R1: BMS × T(M))](table/r1-tm.md)** — 機械検査を通った行のみ掲載
- [作業原則 (constitution)](constitution.md) — 一度誤った値を公開した経験から得た原則。1 枚
- [計画とエビデンスの設計](plan/README.md) — 何を証明することをエビデンスとするか (E1/E2/E3/G/MT)
- [Rathjen の表記系一覧 (強さ順)](rathjen-ordinals.md) — R1〜R5 と最終ターゲット

## 構成

- `lean/` — Lean 4 (v4.30.0, 外部依存なし) による形式化
  - `BMS/` BM4 の行列・辞書式順序・展開・標準形
    ([yaBMS](https://github.com/koteitan/yaBMS) の C 実装との突き合わせ済み)
  - `TM/` Rathjen 𝔗(M) の項・順序・正規形 (Rathjen 1991 §2 に忠実)・基本列
  - `Trans/` 翻訳関数 (o および、オラクル較正済みの oR = dict∘TransPort)
  - `Evidence/` 意味証明書 (`Cert.lean`)、𝔗(M) の順序理論と整礎性 (`WF.lean`)、
    および有限検査器 (順序埋め込み・相互共終・双模倣)
  - `Rows/` 対応表の行データベースと行ごとの機械検査
- `table/` — 生成物 (手編集しない)
- `scripts/crosscheck.sh` — yaBMS との出力照合
- `scripts/standard-audit.sh` — 表の全行が**標準形の行列**であることの検査
- `scripts/oracle-audit.sh` — 表の全行を変換写像 (オラクル) と突き合わせる

## 表の ✅ が主張していること

表の証明列 (✅) は宣言ではなく、証明書レジストリからビルドが**計算**して付ける。
✅ の付いた行については、次がすべて Lean の定理である:

1. その行は、内部に現れる値がすべて 𝔗(M) の項である証明書を持つ (これが登録の条件)
2. そのような証明書の範囲で、掲載値以外の値は取り得ない (上下いずれの側も)
3. 値が 𝔗(M) の外に出るものも含め、**いかなる**証明書も掲載値より上の値を与えない

まだ排除できていないものと、較正事故 (v0.1.41) の経緯は
[計画](plan/README.md) と[表の凡例](table/r1-tm.md)に明記してある。
整礎性の証明は要求せず、「行列 = 順序数」の主張は整礎性を仮定した条件付きで
形式化する方針だが、Γ₀ 未満については整礎性も証明済み。

## 検証と再生成

```sh
cd lean && lake build                      # 全行の検査 (#guard) を含む
lake exe gentable > ../table/r1-tm.md      # 表の再生成
YABMS=/path/to/yaBMS/c/bms ../scripts/crosscheck.sh   # BMS 実装の照合
```
