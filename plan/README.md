# 計画: BMS × Rathjen T(M) 対応表の Lean エビデンス (R1 ステージ)

本リポジトリは、順序数表記と見做した BMS (Bashicu Matrix System) と
Rathjen の順序数崩壊関数の対応表を、Lean による機械検証付きで作ることを目的とする。

最初のターゲットは R1 = Rathjen の表記系 $`T(M)`$:

- M. Rathjen, *Ordinal Notations Based on a Weakly Mahlo Cardinal*,
  Archive for Mathematical Logic 29 (1990) 249–263 — $`T(M)`$, $`\chi_\alpha`$, $`\psi_\kappa`$ の定義
- M. Rathjen, *Proof-theoretic analysis of KPM*,
  Archive for Mathematical Logic 30 (1991) 377–403 — $`T(M)`$ による KPM の解析

表記系の全体像と選定理由は [../rathjen-ordinals.md](../rathjen-ordinals.md) を参照。

## エビデンスの設計(何を証明するか)

整礎性(整列性)の証明は要求せず、「基本列付き表記系としての対応」を証明対象とする。
以下の対象はすべて構文的に定義され、順序・述語は決定可能である
(Lean 上ではここに書いた数式と 1:1 に対応する定義・定理を置く)。

**BMS 側**

- 行列の集合 $`\mathcal{M}`$ と辞書式順序 $`\lt_B`$
- 展開 $`M[n]`$ ($`n`$ 番目の展開。活性化関数の任意化)
- 標準形述語 $`\mathrm{Std}(M)`$ (初期行列からの展開到達性)

**$`T(M)`$ 側** (Rathjen 1991 の構文的定義に忠実)

- 項の集合 $`T`$、項の順序 $`\lt_T`$、正規形述語 $`\mathrm{NF}`$
- 基本列 $`t[n]`$ (本リポジトリで一様に明示定義する)

**翻訳関数** $`o\colon \mathcal{M}\to T`$ (= 対応表の一般化・一様化)

証明する命題は次の 4 群 (E1, E2, E3, G) である。

### E1 (行検査) — 表が単一アルゴリズム $`o`$ の出力であること

表の各行 (行列 $`M_i`$, 項 $`t_i`$) について

```math
o(M_i) = t_i
```

を計算で機械検査する。これ自体は $`o`$ の正しさを主張しない。
「全行が 1 つの $`o`$ から機械的に出た」ことの保証である。

### E3 (展開と基本列の整合) — 本体のエビデンス

添字の規約: BMS の $`M[n]`$ はコピー $`B(0),\dots,B(n)`$ の $`n{+}1`$ 個を並べるため、
$`T(M)`$ 側の基本列とは添字が 1 ずれる ($`o(M[n])`$ は $`t[n{+}1]`$ と対応する)。

**実装後の知見**: BMS の展開列と $`T(M)`$ の基本列は、同じ順序数への
**異なる共終列**になり得る (例: $`\varepsilon_1`$ へ BMS は
$`\varepsilon_0, \varepsilon_0^2, \varepsilon_0^{\varepsilon_0}, \dots`$ で登り、
標準的な fs は $`\varepsilon_0{+}1, \omega^{\varepsilon_0+1}, \dots`$ で登る)。
そこで E3 は等式ではなく**相互共終形**で立てる。行ごとに:

```math
\forall n.\ o(M_i[n]) <_T t_i,
\qquad
\forall n\,\exists k.\ o(M_i[n]) <_T t_i[k],
\qquad
\forall k\,\exists n.\ t_i[k] <_T o(M_i[n])
```

($`\exists`$ は行ごとに具体的な witness 関数で与える)。
両側の列が互いに追い越し合えば上限は一致するので、
これで「$`M_i`$ と $`t_i`$ が同じ極限を指す」ことが担保される。
なお CNF 領域 ($`\varepsilon_0`$ 以下) では添字ずれを除いた等式
$`o(M[n]) = o(M)[n{+}1]`$ がそのまま成り立ち、成り立つ領域ではこちらも記録する。

あわせて $`o`$ が零・後続・極限の分類を保つこと
(後続なら $`o(\mathrm{pred}(M)) = \mathrm{pred}(o(M))`$)。

### G (片側ずつの構造定理) — 展開・基本列の単調性と共終性

E 群がすべて翻訳 $`o`$ に言及する「対応の主張」であるのに対し、
G 群 (G = ground, 土台) は $`o`$ に言及しない。BMS・$`T(M)`$ それぞれ単独の性質
(対応表が正しいか否かに依らず各表記系が持つべき土台)なので、
E の番号とは別のラベルにしている。

$`T(M)`$ 側: 極限の正規形項 $`t`$ と任意の $`s\in\mathrm{NF}`$ について

```math
t[n] <_T t,
\qquad
s <_T t \implies \exists n.\ s <_T t[n].
```

BMS 側: 標準形の $`M, N`$ について

```math
M[n] <_B M,
\qquad
N <_B M \implies \exists n.\ N <_B M[n].
```

### E2 (順序埋め込み) — 照合用

標準形の $`M, N`$ について

```math
o(M) \in \mathrm{NF},
\qquad
M <_B N \iff o(M) <_T o(N).
```

順序は決定可能なので、一般定理の完成前でも個別のペアは計算で即検査できる。

### MT (主定理: 条件付き意味論)

「$`\lt_T`$ の $`\mathrm{NF}`$ 上への制限が整礎」という仮定を $`\mathrm{wf}`$ と書く。
E3 + G + (E2 のうち $`o(M)\in\mathrm{NF}`$) から次が従う:
$`\mathrm{wf}`$ のもとで、任意の標準形 $`M`$ について

```math
\mathrm{otype}\bigl(\{\,N \in \mathcal{M} : \mathrm{Std}(N),\ N <_B M \,\},\ <_B\bigr)
\;=\;
\mathrm{otype}\bigl(\{\, s \in \mathrm{NF} : s <_T o(M) \,\},\ <_T\bigr)
```

($`\mathrm{otype}`$ は順序型)。左辺は「行列 $`M`$ の表す順序数」、
右辺は「項 $`o(M)`$ の表す順序数」だから、これは対応表の行の主張そのものである。

証明の骨格: $`M`$ が極限のとき、G の共終性により両側の below 集合が増大和

```math
\{\,N : N <_B M\,\} = \bigcup_n \{\,N : N <_B M[n]\,\},
\qquad
\{\,s : s <_T o(M)\,\} = \bigcup_n \{\,s : s <_T o(M)[n]\,\}
```

になり、E3 の相互共終により両側の増大和が同じ集合を尽くし、
帰納法の仮定で順序型が一致する(零・後続も同様)。
仮定 $`\mathrm{wf}`$ は紙の上では既知(Rathjen 1994 の整列証明)であり、
そこだけを明示的な仮定として切り出す。

### 各群と MT の関係

MT は「E1〜E3 と G を証明したことが、なぜ対応表のエビデンスになるのか」を
1 枚で示す正当化の定理である。依存関係:

```
E3 (展開↔基本列) + G (両側の共終性) + E2 の一部 (o(M) ∈ NF)
        │
        │  wf を仮定した超限帰納法
        v
MT:  otype(M より下の標準形行列) = otype(o(M) より下の正規形項)
        │
        │  E1 (o(M_i) = t_i) を代入
        v
行 i の最終主張: 行列 M_i の表す順序数 = 項 t_i の表す順序数
```

- E3 + G は MT の証明の材料。
- E1 は MT を表の各行に適用するための入口。
- E2 の順序同値は MT の証明には使わない独立のクロスチェック
  ($`o`$ に誤りがあれば MT より先に E2 の計算検査が落ちる、早期検出の役割)。
- 成果物は 2 層に分かれる:
  **無条件の構文的成果物 = E1, E2, E3, G** /
  **条件付き ($`\mathrm{wf}`$ を仮定) の最終主張 = MT**。

### 恣意性の排除と誤り検出

- $`t[n]`$ と $`o`$ は本リポジトリの定義だが、**一様性**(全項・全行列に対する各 1 つの定義が
  全行で同時に E3 を満たすこと)が内容であり、行ごとの調整による偽装は構造上できない。
  $`T(M)`$ の項・順序・正規形は Rathjen の論文で固定されている。
- 表のある行が誤っていれば、E2 の計算検査(順序の逆転)または
  E3 の具体的な $`n`$(基本列の不一致)が反例として機械的に得られる。
  これは失敗ではなく成果(表の訂正)として報告する。

### 注意

- BMS 側の共終性 ($`N \lt_B M \implies \exists n.\ N \lt_B M[n]`$) が G の最難部で、
  一般の BMS では研究課題。まず表の対象範囲の行列クラスに制限して証明する。
- MT の記述のみ順序数型(mathlib)を要するため mathlib 導入後に行う。
  それまでは E1+E2+E3+G が無条件の構文的成果物である。

## ディレクトリ構成

```
bms-rathjen/
├── README.md                 # 入口: プロジェクト概要 + 対応表へのリンク
├── rathjen-ordinals.md       # Rathjen 表記系の一覧(強さ順)
├── plan/
│   └── README.md             # 本計画書
├── table/                    # 対応表 (GitHub MathJax; 自動生成物。手編集しない)
│   └── r1-tm.md              # BMS × T(M) 対応表
├── lean/                     # Lean 4 (lake) プロジェクト
│   ├── lean-toolchain        # leanprover/lean4:v4.30.0
│   ├── lakefile.lean         # lean_lib: BMS, TM, Trans, Rows, Evidence / lean_exe: gentable
│   ├── BMS.lean              # ライブラリルート
│   ├── BMS/                  # ── BMS 側(表記系として) ──
│   │   ├── Basic.lean        # 行列の表現 (列のリスト)、基本操作、表示
│   │   ├── Order.lean        # 辞書式順序、Decidable インスタンス
│   │   ├── Expand.lean       # 展開 expand : Matrix → Nat → Matrix
│   │   │                     #   活性化関数を任意化し、コピー数 n を引数に取る
│   │   └── Standard.lean     # 標準形述語 = 初期行列からの展開到達性 (witness 付き)
│   ├── TM.lean               # ライブラリルート
│   ├── TM/                   # ── Rathjen T(M) 側 (1990/1991) ──
│   │   ├── Terms.lean        # 項の構文 (0, +, ω^·? , χ_α(β), ψ_κ(α), M など)
│   │   ├── Order.lean        # 項の比較 <_T、Decidable インスタンス
│   │   ├── NF.lean           # 正規形条件 (1990 論文の C-集合条件の構文化)
│   │   └── FS.lean           # 基本列 t[n] の明示定義
│   │                         #   (論文には基本列が無いので、ここが定義の選択になる)
│   ├── Trans.lean            # ライブラリルート
│   ├── Trans/
│   │   └── TM.lean           # 対応写像 o : BMS → T(M) (= 対応表の一般化・一様化)
│   ├── Rows.lean             # ライブラリルート
│   ├── Rows/
│   │   └── TM.lean           # 表の行データベース (行列, 項, 備考) + 行ごとの E1/E3 補題
│   ├── Evidence.lean         # ライブラリルート
│   ├── Evidence/
│   │   └── TM.lean           # 一般定理 (E2 順序埋め込み、G 構造定理、MT。長期目標)
│   ├── Test/
│   │   └── CrossCheck.lean   # #eval によるスモークテスト (展開・比較の具体例)
│   └── Main.lean             # lean_exe gentable: 行 DB → table/r1-tm.md を標準出力に生成
├── scripts/
│   └── crosscheck.sh         # yaBMS (C 実装) と Lean の展開/比較/標準形判定の突き合わせ
└── .github/
    └── workflows/
        └── ci.yml            # lake build + gentable の出力が table/ と一致するか検査
```

### 各部の役割と方針

- **BMS/**: 行列は `List (List Nat)`(列のリスト)で表現し、行数は固定しない。
  展開規則は数式的定義に従い、活性化関数は固定せずコピー数 `n : Nat` を
  展開の引数として与える(これにより行列は `[n]` なしの順序数表記として扱える)。
  実装の正しさは [yaBMS](https://github.com/koteitan/yaBMS) の C 実装
  (展開・大小比較・標準形判定)との出力照合 (`scripts/crosscheck.sh`) で担保する。
- **TM/**: 1990 論文の $`T(M)`$ を項システムとして構文化する。
  比較 `<_T` と正規形は論文の定義から決定可能手続きとして書き下す。
  基本列 `FS` は論文に無いため、コミュニティの慣用(UNOCF 等)を参考に明示定義し、
  定義の出典・選択理由をコメントで残す。
- **Trans/**: 対応写像 $`o`$。ここが本プロジェクトの研究部分であり、
  E2/E3 が落ちる場合は $`o`$(または表)の誤りが反例として検出される。
- **Rows/**: 表の行を Lean のデータとして一元管理する
  (行列、$`T(M)`$ 項、対応表の MathJax 文字列は項から自動生成)。
  1 行 = 1 補題群 (E1: `rfl`、E3: `n` 上の帰納法)。
  - **命名規約**: 行の名前空間は行列リテラルそのもの
    (Lean 4 の `«...»` 識別子。例: `«(0,0,0)(1,1,0)»`)。連番は使わない
    (行の挿入で番号がずれるため)。中身は全行共通で
    `M`(行列), `t`(項), `e1`, `e3`。
    例: `«(0,0,0)(1,1,0)».e3 : ∀ n, o (expand M n) = fs t n`。
  - E2 の行ごとインスタンスと正規形検査は、行ごとには名前を持たせず、
    行 DB 全体への一括定理にする:
    `rows_sorted_B`(BMS 順に整列), `rows_sorted_T`($`T(M)`$ 順に整列),
    `rows_nf`(全項が正規形)を `decide` で検査。
    行の追加・挿入時も自動で全行再検査される。
- **Main.lean (gentable)**: `lake exe gentable > ../table/r1-tm.md` で表を生成する。
  表の唯一の情報源は Rows/ であり、`table/` は生成物としてコミットする。
- **依存関係**: 当面は外部依存なし(mathlib 不使用)で始める。
  構文的な E1〜E3・G には core の `Decidable` と `List` で足りる見込み。
  MT の記述(順序数型が必要)に進む段階でのみ mathlib
  (pss-proof と同じ v4.30.0 固定)の導入を検討する。
- **toolchain**: [pss-proof](https://github.com/koteitan/pss-proof) と同じ
  `leanprover/lean4:v4.30.0` に揃える(検証環境を共有するため)。

## 作業ステージ (R1 内の順序)

1. **S0 骨組み**: lake プロジェクト、`BMS/Basic,Order,Expand`、yaBMS との crosscheck
2. **S1 T(M) 構文**: `TM/Terms,Order,NF`(1990 論文 §1–§4 の構文化)
3. **S2 基本列**: `TM/FS` の定義と、単調性・共終性の一般補題 (Evidence)
4. **S3 変換**: `Trans/TM` の $`o`$ を、まず既知の予想対応の浅い部分
   ($`\psi(I)`$ 以下 → 3 行行列の先頭部分)から定義
5. **S4 行の量産**: `Rows/TM` に行を追加しながら E1/E3 補題を付け、
   `gentable` で `table/r1-tm.md` を生成
6. **S5 一般定理**: E2・E3 一般形・G を標準形上で証明し、
   mathlib 導入後に MT を記述(長期)

R2 ($`T(K)`$, *Proof theory of reflection*) 以降は `TK/`・`Trans/TK.lean`・
`Rows/TK.lean`・`table/r2-tk.md` を同じ形で追加してスケールさせる。

## 記述ルール

- 公開リポジトリのため、ローカル環境のパスには言及しない。
  出典は論文の書誌情報と公開 URL (GitHub リポジトリ等) で示す。
- 対応表・文書の数式は GitHub で描画される MathJax (`$`...`$`) を用いる。
- `table/` 配下は生成物。手編集せず、必ず `Rows/` を編集して再生成する。
