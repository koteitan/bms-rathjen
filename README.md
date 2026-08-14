# bms-rathjen

順序数表記と見做した BMS (Bashicu Matrix System) と、Rathjen の順序数崩壊関数の
対応表を、Lean による機械検証付きで作るプロジェクト。

読む場所は目的で分かれる。

- **[対応表 (R1: BMS × T(M))](table/table-r1.md)** — 表だけならファイル冒頭。
  行が満たす命題は同ファイルの[証明の仕様](table/table-r1.md#証明の仕様) (`E.` / `D.` / `T.`)
- [作業仕様](plan/README.md) — どう作るか。手順・命名規則・ビルド・資料の場所
- [原則 (constitutions)](plan/constitutions.md) — 文書の書き方と、何を証拠と呼ぶか。1 枚
- [表の仕様](plan/spec.md) — 対応表に何を載せるか
- [Rathjen の表記系一覧 (強さ順)](rathjen-ordinals.md) — R1〜R5 と最終ターゲット
- [外部の対応表との差分](table/diff.md) — 一致した範囲、証明で決着した 6 行、未決の 3 行

## 構成

- `lean/` — Lean 4 (v4.30.0, 外部依存なし) による形式化
  - `BMS/` BM4 の行列・辞書式順序・展開・標準形
    ([yaBMS](https://github.com/koteitan/yaBMS) の C 実装との突き合わせ済み)
  - `TM/` Rathjen 𝔗(M) の項・順序・正規形 (Rathjen 1991 §2 に忠実)・基本列
  - `Trans/` 翻訳関数 (o および、参照実装で較正済みの oR = dict∘TransPort)
  - `Evidence/` 意味証明書 (`Cert.lean`)、𝔗(M) の順序理論と整礎性 (`WF.lean`)、
    および有限検査器 (順序埋め込み・相互共終・双模倣)
  - `Rows/` 対応表の行データベースと行ごとの機械検査
- `table/` — 生成物 (手編集しない)
- `scripts/` — 検査器。**それぞれ自己試験を持つ** (下記)

## 表の ✅ が主張していること

表の証明列は宣言ではなく、ビルドが**計算**して付ける。✅ は証明書レジストリから、
$`f_n`$ は行が指す名前空間を証明ファイルから探して付ける (見つからなければ印は出ない)。
✅ の付いた行については、次がすべて Lean の定理である:

1. その行は、内部に現れる値がすべて 𝔗(M) の項である証明書を持つ (これが登録の条件)
2. そのような証明書の範囲で、掲載値以外の値は取り得ない (上下いずれの側も)
3. 値が 𝔗(M) の外に出るものも含め、**いかなる**証明書も掲載値より上の値を与えない

まだ排除できていないものと、較正事故 (v0.1.41) の経緯は
[作業仕様](plan/README.md) と[表の証明の仕様](table/table-r1.md#証明の仕様)に明記してある。
整礎性の証明は要求せず、「行列 = 順序数」の主張は整礎性を仮定した条件付きで
形式化する方針だが、Γ₀ 未満については整礎性も証明済み。

## 検証と再生成

```sh
cd lean && lake build                      # 全行の検査 (#guard) を含む
lake exe gentable > ../table/table-r1.md      # 表の再生成
YABMS=/path/to/yaBMS/c/bms ../scripts/crosscheck.sh   # BMS 実装の照合
```

## 検査器と、その試験

検査器はそれぞれ自己試験を持つ。方針は
[原則 C5](plan/constitutions.md#c5-検査器は自分の試験を持つ)、一覧は
[作業仕様](plan/README.md#突き合わせのスクリプト) にある。

| 検査器 | 何を測るか | 試験の走らせ方 |
|---|---|---|
| `lean/scripts/axiom_sweep.lean` | リポジトリ全体が何に依存しているか | ファイル内の `#guard` と、`axioms_of` の自己試験が規則を共有 |
| `lean/scripts/axioms_of.lean` | 宣言ごとの公理 | `lake env lean scripts/axioms_of.lean` — 4 分類 + 5 集計を検査 |
| `scripts/check-math.js` | 数式が GitHub で壊れるか、リンクとアンカーが生きているか | 引数に `.md` を渡す。アンカー規則は GitHub 実測の 7 例で自己試験 |
| `scripts/settled.sh` | 作業役がファイルを書き終えたか | `scripts/settled.sh --self-test` — 5 ケース |
| `scripts/standard-audit.sh` | 表の全行が標準形の行列か | |
| `scripts/crosscheck.sh` | BMS の実装が yaBMS の C 実装と一致するか | 112 例そのものが試験 |
| `scripts/refimpl-audit.sh` | 表の全行が変換写像と一致するか | |

## ライセンス

**CC BY-SA 3.0** ([LICENSE](LICENSE))。

`lean/Trans/Recal.lean` は naruyoko 氏の
[pss-vs-buchholz](https://github.com/Naruyoko/googology/tree/main/pss-vs-buchholz)
の `common.js` の移植 (CC BY-SA 3.0)。

## 参考文献

**依拠しているものだけを挙げる** — 定義を写したもの、コードの移植元、値を突き合わせた相手、
論証で引いたもの。読んだが採らなかったものは [plan/README-old.md](plan/README-old.md) の調査表にある。
実装は当該ファイルが git に入った年を挙げ、突き合わせに使った版の日付を併記する。

### 定義の出典

- 1986, W. Buchholz, "A new system of proof-theoretic ordinal functions",
  Ann. Pure Appl. Logic 32 — $`\mathrm{OT}_B`$。`lean/Trans/Dict.lean` の始点
- 1990, M. Rathjen, "Ordinal notations based on a weakly Mahlo cardinal",
  Arch. Math. Logic 29 — $`\mathfrak{T}(M)`$、$`\chi`$、$`\psi`$
- 1991, M. Rathjen, "Proof-theoretic analysis of KPM",
  Arch. Math. Logic 30 — $`\mathfrak{T}(M)`$ の自己完結した構文的定義。`lean/TM/` はこの §2 に従う
- 1994, M. Rathjen, "Collapsing functions based on recursively large ordinals:
  a well-ordering proof for KPM", Arch. Math. Logic 33 — 再帰的な再構成
- 2018, koteitan, "[バシク行列の数式的定義](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E6%95%B0%E5%BC%8F%E7%9A%84%E5%AE%9A%E7%BE%A9)",
  巨大数研究 Wiki ブログ — `lean/BMS/` が従う展開規則
- 2019, P進大好きbot, "[Cheatsheet on Properties of OCFs](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Cheatsheet_on_Properties_of_OCFs)",
  Googology Wiki Blog — $`\psi`$ の引数の制限。[plan/chi-2ary.md](plan/chi-2ary.md) で引いている

### 突き合わせた実装・対応表

- 2018, koteitan, "yaBMS", github.com — BMS の C 実装 (2026-01-10 版)。`scripts/crosscheck.sh` が 112 例で照合
- 2022, naruyoko, "padicBotRathjen", github.com — $`\mathfrak{T}(M)`$ の独立実装 (`implementation.js`、2022-01-08 版)。
  `scripts/padicbot-ref.js` が参照実装として走らせる
- 2023, Hexirp, "[バシク行列システム４と全部盛りオクフ・ベータの対応](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC:Hexirp/%E3%83%96%E3%83%AD%E3%82%B0)",
  巨大数研究 Wiki ブログ (2023-09-16〜2023-11-18 の解析)
  — [差分](table/diff.md)で 390 行を突き合わせた
- 2024, naruyoko, "pss-vs-buchholz", github.com — `lean/Trans/Recal.lean` はこの `common.js` (2026-08-12 版) の移植
- n.d., 著者未確認, "[BM4-Analysis](https://docs.google.com/spreadsheets/d/1Y4BV65KNPjJ6uBtBBFYDXKo6PFlmEuowyn39XmLh4MI/edit?usp=sharing)",
  Google Sheets — [表記系一覧](rathjen-ordinals.md)の到達点の対応
