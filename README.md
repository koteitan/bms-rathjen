# bms-rathjen

順序数表記と見做した BMS (Bashicu Matrix System) と、Rathjen の順序数崩壊関数の
対応表を、Lean による機械検証付きで作るプロジェクト。

読む場所は目的で分かれる。

- **[対応表 (R1: BMS × T(M))](table/table-r1.md)** — 表だけならファイル冒頭。
  行が満たす命題は同ファイルの[エビデンス節](table/table-r1.md#エビデンス) (`E.` / `P.` / `D.`)
- [設計方法と記録](plan/README.md) — どう作るか、何を撤回したか
- [作業原則 (constitutions)](plan/constitutions.md) — 一度誤った値を公開した経験から得た原則。1 枚
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
- `scripts/` — 検査器。**それぞれ自己試験を持つ** (下記)

## 表の ✅ が主張していること

表の証明列 (✅) は宣言ではなく、証明書レジストリからビルドが**計算**して付ける。
✅ の付いた行については、次がすべて Lean の定理である:

1. その行は、内部に現れる値がすべて 𝔗(M) の項である証明書を持つ (これが登録の条件)
2. そのような証明書の範囲で、掲載値以外の値は取り得ない (上下いずれの側も)
3. 値が 𝔗(M) の外に出るものも含め、**いかなる**証明書も掲載値より上の値を与えない

まだ排除できていないものと、較正事故 (v0.1.41) の経緯は
[計画](plan/README.md) と[表のエビデンス節](table/table-r1.md#エビデンス)に明記してある。
整礎性の証明は要求せず、「行列 = 順序数」の主張は整礎性を仮定した条件付きで
形式化する方針だが、Γ₀ 未満については整礎性も証明済み。

## 検証と再生成

```sh
cd lean && lake build                      # 全行の検査 (#guard) を含む
lake exe gentable > ../table/table-r1.md      # 表の再生成
YABMS=/path/to/yaBMS/c/bms ../scripts/crosscheck.sh   # BMS 実装の照合
```

## 検査器と、その試験

**この repo の検査器は、自分自身の試験を持っている。** 理由は
[constitutions C0](plan/constitutions.md) にある — 一晩に自作の検査器が 5 回誤り、
そのうち**事前に試験してあった 1 つだけが最初から正しかった**。残る 4 つは、
誤った答えを出した後で試験を書いている。

| 検査器 | 何を測るか | 試験の走らせ方 |
|---|---|---|
| `lean/scripts/axiom_sweep.lean` | リポジトリ全体が何に依存しているか | ファイル内の `#guard` と、`axioms_of` の自己試験が規則を共有 |
| `lean/scripts/axioms_of.lean` | 宣言ごとの公理 | `lake env lean scripts/axioms_of.lean` — 4 分類 + 5 集計を検査 |
| `scripts/check-math.js` | 数式が GitHub で壊れるか、リンクとアンカーが生きているか | 引数に `.md` を渡す。アンカー規則は GitHub 実測の 7 例で自己試験 |
| `scripts/settled.sh` | 作業役がファイルを書き終えたか | `scripts/settled.sh --self-test` — 5 ケース |
| `scripts/standard-audit.sh` | 表の全行が標準形の行列か | |
| `scripts/crosscheck.sh` | BMS の実装が yaBMS の C 実装と一致するか | 112 例そのものが試験 |
| `scripts/oracle-audit.sh` | 表の全行が変換写像と一致するか | |

**試験は両側を見る。** 欠陥を検出できることだけ確かめても、**常に赤を返す検査器と
区別がつかない**。正常な対照で沈黙することまで見て、初めて検出したと言える。
`check-math.js` は 5 種類の欠陥 + 正常な文書、`settled.sh` は 5 ケース、
`axioms_of.lean` は公理なし・propext のみ・選択公理・`native_decide`・`sorry` の
5 種類を振り分ける。

**そして試験自体も、故意に壊して確かめてある。** 今夜、自己試験が 2 回とも盲目だった
— 片方は集計の層を通っていなかった (そこにバグがあった)、もう片方は陽性対照が無く、
計数を潰しても「0 件」で通った。**「自己試験が通った」は、その試験を壊してみるまで
根拠にならない。**

## ライセンス

**CC BY-SA 3.0** ([LICENSE](LICENSE))。Googology Wiki (Fandom) と同じライセンスに
揃えてある。突き合わせに使う外部の解析がそこで公開されており、双方向に素材が行き来
できるようにするため。

外部資料はリポジトリに入れない。実行時にディレクトリを渡して読み、URL で引用する
(`scripts/external-check.py`、`scripts/hexirp-rathjen-check.py`)。出典が正で、
ローカルの控えは複製にすぎない。

`lean/` を別ライセンスのソフトウェアで再利用したい場合は issue を。CC BY-SA は
コンテンツ向けで、ソース提供条項も特許条項も無く、GPL 系と互換性が無い。
