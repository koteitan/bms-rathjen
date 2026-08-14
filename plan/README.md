# 作業仕様

**この文書は「どう作業するか」だけを書く。**

| 知りたいこと | 行き先 |
|---|---|
| 表が何を主張しているか | [table/table-r1.md](../table/table-r1.md) の証明の仕様 |
| 表に何を載せるか | [plan/spec.md](spec.md) |
| 書くとき・読むときの原則 | [plan/constitutions.md](constitutions.md) |
| 過去に何を失敗したか | [plan/README-old.md](README-old.md) |
| 外部の対応表との差分 | [table/diff.md](../table/diff.md) |
| 作業役 (codex) への毎回同じ指示 | [plan/worker-spec.md](worker-spec.md) |
| $`\chi`$ を 2 引数にする話 | [plan/chi-2ary.md](chi-2ary.md) |

## 何を作っているか

BMS の行列 $`M`$ と Rathjen $`\mathfrak{T}(M)`$ の項 $`t`$ の対応表を作り、
行ごとに `E.cert` を Lean の定理にして ✅ を付ける。

**Lean のコードが成果物で、ビルドがテストである。** 表もビルドの生成物であり、
手で書ける部分は無い。

## ビルドと検査

`lean/` で実行する。

| コマンド | 何をするか |
|---|---|
| `lake build` | 全体。`#guard` が全部通ることがテストである。0 errors 以外は失敗 |
| `lake exe gentable > ../table/table-r1.md` | 表の再生成。`Rows/` を触ったら必ず走らせる |
| `lake env lean Rows/G11.lean` | 1 ファイルだけ確認 |

`lake build` は `.lake/` に書き込むので、**同時に 2 つ走らせてはいけない**。
複数の作業者が並行するときは、ビルドは 1 人が持ち、ほかは 1 ファイルの検査だけを行う。

受け入れの条件は 3 つとも満たすことである。

1. ビルドが exit 0
2. `#print axioms <定理名>` に `sorryAx` が無い (`Classical.choice` は可、`native_decide` は不可)
3. **定理の文が、頼まれた文になっている** — 弱めた文が通っても受け入れない

`sorry` と `native_decide` は使わない。`lean/scripts/axiom_sweep.lean` が全宣言を走査して
数を出すので、作業の前後で `sorryAx 0` と `native 0` を確かめる。

## ディレクトリ構成

```
bms-rathjen/
├── README.md              入口
├── rathjen-ordinals.md    Rathjen 表記系の一覧 (強さ順、R1〜R5)
├── plan/
│   ├── README.md          この文書 (作業仕様)
│   ├── spec.md            table/ の仕様
│   ├── constitutions.md   書き方の原則
│   └── README-old.md      旧計画書 (失敗の記録)
├── table/
│   ├── table-r1.md        対応表 (生成物。手編集しない)
│   └── diff.md            外部の対応表との差分
├── lean/
│   ├── BMS/               BMS 側。行列・辞書式順序・展開・標準形
│   ├── TM/                Rathjen 側。項・順序・正規形・基本列
│   ├── Trans/             翻訳。BMS → Buchholz → T(M)
│   ├── Rows/              表の行データベースと、行ごとの証明
│   ├── Evidence/          一般定理。証明書・整礎性・有限検査器
│   ├── Test/              スモークテスト
│   ├── Main.lean          gentable の本体
│   └── scripts/           公理掃引などの単発スクリプト
└── scripts/               外部実装との突き合わせ (shell / node / python)
```

### 各ディレクトリの決まり

- **`BMS/`** — [koteitan の数式的定義](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E6%95%B0%E5%BC%8F%E7%9A%84%E5%AE%9A%E7%BE%A9)
  に従う。行列は `List (List Nat)` (列のリスト)、行数は固定しない。
  活性化関数は固定せず、コピー数 `n : Nat` を展開の引数に取る。
  実装が正しいかは yaBMS の C 実装との照合 (`scripts/crosscheck.sh`) で見る
- **`TM/`** — Rathjen の論文に忠実に写す。**すべての定義に、論文の節番号を書いたコメントを付ける**。
  基本列 `FS.lean` だけは論文に無いので設計であり、変えると全行の証明が落ちる。凍結して扱う
- **`Trans/`** — 翻訳。ここが研究の部分である
- **`Rows/`** — `TM.lean` が行データベース、その他が行ごとの証明。1 行 = 1 名前空間
- **`Evidence/`** — 行に依存しない一般定理

## 命名規則

### 行の名前空間

`Rows/` の 1 行は 1 名前空間である。名前は 2 通り。

- 行列そのもの — `«(0,0)(1,1)(2,1)(1,0)»` (Lean 4 のフランス引用符識別子)
- 短い記号 — `F1`、`G3` など。行列が長すぎて識別子にすると読めない行に使う

**連番を行の順序に使わない。** 行を挿入すると番号がずれる。

行データベースの `Row.proof` にその名前を `"namespace G3"` の形で書くと、
gentable が証明ファイルを探して $`f_n`$ 印のリンクを作る。**名前が見つからなければ
印は出ない** — 実体の無い印は原理的に残らない。

### 名前空間の中身

`oR` の等式を作る行は、4 つの定義と 4 つの定理をこの名前で持つ。

| 名前 | 型 |
|---|---|
| `M` | `BMS.Matrix` — この行の行列 |
| `t` | `Term` — この行の値 |
| `L` | `Nat → Trans.Recal.PS` — 展開が作る梯子 |
| `LBT` | `Nat → Trans.Dict.BT` — その Buchholz 像 |
| `ofMatrix_M` | `∀ n, Trans.Recal.ofMatrix (BMS.expand M n) = some (L …)` |
| `transPort_L` | `∀ m, Trans.Recal.transPort (L m) = LBT m` |
| `dict_LBT` | `∀ n, Trans.Dict.dict (LBT …) = <値>` |
| `oR_M` | `∀ n, Trans.oR (BMS.expand M n) = some (<値>)` |

`oR_M` が最終成果で、ほかの 3 つはその 3 リンクである。

### そのほか

- 補題は `<関数名>_<対象>` — `fpar_A`、`length_K`、`transPort_L`
- 陰性対照は `_not_` を入れる — `cert_row_not_eps0_times_two`
- 節の見出しは `/-! ## §N …  -/`。番号は使い回さない

## 行を足す

3 つの型がある。どれも最後は同じで、`table/table-r1.md` の証明の仕様に従った
Lean のコードを書くことである。

### A. 1 行だけ足す

1. **翻訳の方針を決める** — その行列の展開が `oR` の中でどう動くかを**測る**。
   読んで予想しない。`#eval` で 5〜10 個の `n` について実際の値を出す
2. **翻訳を Lean で書く** — `L` と `LBT` を定義し、`ofMatrix_M` / `transPort_L` /
   `dict_LBT` を証明して `oR_M` に合成する
3. **証明の仕様に従った証明を書く** — `E.cert` (`CertifiedIn(DomI, M, t)`) を証明し、
   `Evidence.Cert.certRows` に登録する。登録だけ足すとビルドが落ちる
4. `Rows/TM.lean` に行を足し、`gentable` で表を作り直す

### B. 区間をまとめて足す (一般化証明)

1 行ではなく「$`\varepsilon_0`$ 未満の全標準行列」のような区間を一度に片付ける。

1. 翻訳の方針を決める (A と同じ。ただし**区間全体で**測る)
2. 翻訳を Lean で書く — 行列の族をパラメータで書き、族についての等式を証明する
3. 証明の仕様に従った証明を書く — 族についての `E.cert` を証明する
4. `Rows/TM.lean` の `regions` に区間行を足す

### C. 一般化から特殊例を出す

B が済んでいる区間の中の 1 行を、表に出したいとき。

1. 証明の仕様に従った証明を書く — 一般定理を具体的な行列に当てる
2. `Rows/TM.lean` に行を足して再生成する

翻訳を書く手間は無い。**B が済んでいるかを先に確かめること** — 済んでいなければ A である。

## E.cert を証明する手順

`E.cert` = `CertifiedIn(DomI, M, t)`。行の種別で使う規則が決まる。

| `kind M` | 規則 | やること |
|---|---|---|
| 空 | `D.CertifiedIn.zero` | 無条件 |
| 後続 | `D.CertifiedIn.succ` | 全展開が同じ $`t`$ を認証することを示す |
| 極限 | `D.CertifiedIn.lim` | 列 $`f`$ を 1 つ与えて 4 連言を示す |

極限行が本体で、4 連言はこうである。

1. $`\forall n.\ \mathrm{CertifiedIn}(\mathrm{DomI}, M[n], f_n)`$ — **展開そのものにも証明書が要る (再帰)**
2. $`\forall n.\ f_n \lt t`$
3. $`\forall n.\ f_n \lt f_{n+1}`$
4. $`\forall s \in \mathfrak{T}(M).\ s \lt t \to \exists n.\ s \le f_n`$ — 共終性

**$`f_n`$ 印は第 1 連言の「値」を与えるだけである。** 印が付いていても残り 3 連言と、
第 1 連言の証明書の側は手つかずである。順に、

1. まず 4 の共終性が既にある範囲かを確かめる。無ければそれが最大の仕事である
2. $`f`$ は自由に選んでよい。$`\mathfrak{T}(M)`$ の標準基本列である必要は無い。
   `Evidence/WF.lean` の `fsC` について 4 連言が揃っている範囲ならそれを使う
3. 2 と 3 は順序の補題で片付く
4. 1 は展開についての再帰。族の定理があるならそれを当てる
5. **陰性対照を書く** — その行に誤った値を認証しようとすると潰れることを示す。
   これが無いと ✅ は「上限を確かめていない印」になる

## 資料

すべて公開されている。**ローカルに落としてある場所は `.claude/skills/bms-rathjen-lean/` に
書いてある。**

### 定義の出典

- 1986, W. Buchholz, "A new system of proof-theoretic ordinal functions",
  Ann. Pure Appl. Logic 32 — $`\mathrm{OT}_B`$
- 1990, M. Rathjen, "Ordinal notations based on a weakly Mahlo cardinal",
  Arch. Math. Logic 29 — $`\mathfrak{T}(M)`$、$`\chi`$、$`\psi`$
- 1991, M. Rathjen, "Proof-theoretic analysis of KPM",
  Arch. Math. Logic 30 — **`TM/` はこの §2 に従う**
- 1994, M. Rathjen, "Collapsing functions based on recursively large ordinals:
  a well-ordering proof for KPM", Arch. Math. Logic 33
- 2018, koteitan, "[バシク行列の数式的定義](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E6%95%B0%E5%BC%8F%E7%9A%84%E5%AE%9A%E7%BE%A9)",
  巨大数研究 Wiki ブログ — **`BMS/` はこれに従う**
- 2019, P進大好きbot, "[Cheatsheet on Properties of OCFs](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Cheatsheet_on_Properties_of_OCFs)",
  Googology Wiki Blog

### 突き合わせる対応表

- 2023, Hexirp, "[バシク行列システム４と全部盛りオクフ・ベータの対応](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC:Hexirp/%E3%83%96%E3%83%AD%E3%82%B0)",
  巨大数研究 Wiki ブログ — 差分は [table/diff.md](../table/diff.md)
- n.d., 著者未確認, "[BM4-Analysis](https://docs.google.com/spreadsheets/d/1Y4BV65KNPjJ6uBtBBFYDXKo6PFlmEuowyn39XmLh4MI/edit?usp=sharing)",
  Google Sheets

## プログラム

**リポジトリに取り込まない。外部から呼ぶ。** naruyoko 氏の実装は CC BY-SA 3.0 で、
`Trans/Recal.lean` はその移植である。

| 何 | 何ができるか | この repo での使い道 |
|---|---|---|
| [yaBMS](https://github.com/koteitan/yaBMS) | BMS の展開・標準形判定・比較 (C 実装) | `scripts/crosscheck.sh` が `BMS/` と 112 例で照合 |
| [pss-vs-buchholz](https://github.com/Naruyoko/googology/tree/main/pss-vs-buchholz) | BMS → Buchholz の変換写像 (`pss2bp`) | **`Trans/Recal.lean` の移植元**。表の Buchholz 列はこの出力 |
| [padicBotRathjen](https://github.com/Naruyoko/googology/tree/main/padicBotRathjen) | $`\mathfrak{T}(M)`$ の独立実装 | `TM/` の順序・正規形・基本列の外部対照。`scripts/padicbot-ref.js` から呼ぶ |

読むなら <https://naruyoko.github.io/googology/> が読みやすい。

## 突き合わせのスクリプト

`scripts/` にある。どれも**自己試験を持つ** — `--self-test` で、捕まえるはずの欠陥を
入れて発火し、正常な対照で沈黙することまで確かめる。

| スクリプト | 何を見るか |
|---|---|
| `crosscheck.sh` | `BMS/` が yaBMS の C 実装と一致するか |
| `standard-audit.sh` | 表の全行が標準形の行列か |
| `refimpl-audit.sh` | 表の全行が変換写像と一致するか |
| `padicbot-ref.js` | `TM/` の順序・正規形を独立実装と突き合わせる |
| `hexirp-rathjen-check.py` | Hexirp の対応表との差分 |
| `check-math.js` | `.md` の数式が GitHub で描画されるか |
| `settled.sh` | 作業者がファイルを書き終えたか |
