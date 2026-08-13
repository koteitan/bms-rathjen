# step.md — 選定 23 行に ✅ を付ける

## ゴール

**対応表 [table/table-r1.md](table/table-r1.md) の「E 証明の対象行」23 行すべてに ✅ を付ける。**

✅ は宣言ではなくビルドが計算して付ける印で、その行が
`Evidence.Cert.certRows` に登録されているときだけ出る。登録の条件は
`CertifiedIn DomI M t` — つまり **23 行それぞれについてその証明を書くこと**が仕事の中身である。

### 完了の判定

```sh
cd lean && leanman build && lake exe gentable > ../table/table-r1.md
```

を通した上で、次の 3 つが全部成り立てば完了:

| 判定 | 見るところ | 今 | 目標 |
|---|---|---|---|
| 選定 23 行に ✅ | `table/table-r1.md` の「証明」列 | **3** | **23** |
| 選定 23 行に $`f_n`$ | 同上 (✅ の前段) | **13** | **23** |
| 未決の行が 0 | `table/diff.md` の「食い違う 9 行」 | 3 行未決 | 0 |

数え方 (Lean で):

```lean
import Rows.Selected
open Rows
def cert (r : Row) : Bool := Evidence.Cert.certRows.any (fun p => p.1 == r.m && p.2 == r.t)
#eval (Rows.Selected.selected.length,
       (Rows.Selected.selected.filter cert).length,
       (Rows.Selected.selected.filter (fun r => r.proof != "")).length)
-- 今: (23, 3, 13) → 目標: (23, 23, 23)
```

そして [table/diff.md](table/diff.md) 末尾の作業ツリーの葉が全部 ✅ になること。

---

## 今どこにいるか

作業ツリーの **1 は済み**。残りは 2・3・4・5 で、中身はこうである。

| | やること | 状態 | ゴールへの効き方 |
|---|---|---|---|
| **2** | `oR` が要る 12 行の $`f_n`$ | 2/12 | $`f_n`$ 列を 13 → 23 にする |
| **3** | ✅ への昇格 | 未着手 | **✅ 列を 3 → 23 にする。本丸** |
| **4** | 外部の表との決着 (族 4 の 3 行) | 6/9 決着 | 未決 3 → 0。2 の副産物 |
| **5** | 付随 3 件 | 未着手 | ✅ には効かない。片付け |

**2 だけ終えても ✅ は 1 つも増えない。** $`f_n`$ は ✅ が要求する 4 連言のうち
第 1 連言の「値」を与えるだけである。**✅ を増やすのは 3 である。**

## やる順序

```
2 (10 行) ──→ 4 (3 行の決着は 2 の副産物)
   │
   └──→ 3 (✅ 本体)  ←── ここが一番重い

5 は独立。いつやってもよい
```

- **2 → 3** の順にする。3 の第 1 連言は各展開の証明書を要求するので、
  展開の値が閉じた形で分かっていないと組めない。2 がその形を与える。
- **4 は 2 の副産物**。族 4 の 3 行の $`f_n`$ が定理になれば、そのまま反証に使える。
- **3 の中で一番大きいのは「Veblen 断片の共終性」**。共終性の一般形は今 CNF 断片
  (`CN t`) にしかなく、選定行は ζ₀ まわりの Veblen 断片にある。ここを伸ばさないと
  選定行は 1 行も ✅ にならない。**3 に入ったら最初にこれを見積もること。**

---

## 検証と受け入れ

```sh
leanman check -C <repo>/lean <file>.lean; echo "exit=$?"
```

- **`lake build` / `lake env lean` / `lean` を直接叩かない。** `.lake` を壊す。
  全体を通すのは `leanman build` (これだけは可。他の作業役と同時に走らせない)。
- `-C` は毎回付ける。同じマシンに別の Lean プロジェクトが居ることがある。
- **判定は終了コードだけ。** `lean` は成功時に何も出さないので、出力が空でも証明できたことにならない。
  `0` green / `1` sorry / `2` error / `124` timeout / `143` killed (124・143 は「決まっていない」)。
- 停止しないかもしれない証明 (`decide`、深い `simp`) は `--backend lean` を付ける。

**「証明できた」は 3 つ揃って初めて言える:**

1. `leanman check` が exit 0
2. `#print axioms <定理名>` に `sorryAx` が無い
3. 主張が頼まれたものと同じ (`theorem` の文をそのまま読む)

1 だけでは足りない。エラーのあるファイルで exit 0 が返り `sorryAx` が出た事故がある。

**禁止**: `sorry`、`native_decide`、`Classical.choice` を増やすこと。

---

## 2. `oR` が要る 12 行の $`f_n`$ — 残り 10 行

### 何を作るか (仕様)

**残り 10 行それぞれについて、`lean/Rows/Selected.lean` に名前空間を 1 つ増やす。**
中身は次の 4 つの定理で、名前と型はこの形に固定する (`G3` は行ごとの新しい名前)。

```lean
namespace G3

def M : BMS.Matrix := <その行の行列>          -- Rows/TM.lean の `rows` にある行と一致させる
def t : Term       := <その行の項>            -- 同上
def L (m : Nat) : Trans.Recal.PS   := <梯子>   -- predP (L (m+1)) = L m を満たす形に取る
def LBT (m : Nat) : Trans.Dict.BT  := <BT 側の像>

/-- リンク 1 -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n) = some (L (n+1))

/-- リンク 2 -/
theorem transPort_L (m : Nat) : Trans.Recal.transPort (L m) = LBT m

/-- リンク 3 -/
theorem dict_LBT (n : Nat) : Trans.Dict.dict (LBT (n+1)) = <f n>

/-- 行の主張。これが成果物 -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n) = some (<f n>)

end G3
```

`<f n>` は行によって 2 種類ある。

- **一様なずらし `j` がある行** (下の表で「ずらし」に数字がある 4 行) → `fsN t (n+j)`
- **無い行** (残り 6 行) → `Rows.Selected` に既にある `fA`〜`fF` のどれか。
  **`fsN t` に乗らないので `fsN` を目標にしてはいけない** (下記「$`f_n`$ が `fsN` に乗らない 6 行」)。

そして `lean/Rows/TM.lean` のその行に `proof := "namespace G3"` を足す。

### 通すべきテスト

```lean
-- Rows/Selected.lean に置く
#guard (List.range 6).all fun n => Trans.oR (BMS.expand G3.M n) == some (<f n>)
#guard rest12.any fun r => r.m == G3.M && r.t == G3.t          -- 表の行と結ぶ
#guard (rows.filter fun r => r.proof == "namespace G3").length == 1
```

```sh
leanman check -C <repo>/lean lean/Rows/Selected.lean   # exit 0
```

```lean
#print axioms G3.oR_M     -- [propext, Quot.sound] 以下。Classical.choice が出たら直す
```

10 行ぶん終わったときの最終テスト:

```lean
#eval (Rows.Selected.selected.filter (fun r => r.proof != "")).length   -- 23 になること
```

### どう作るか

`Rows.Selected.G1` (`(0,0)(1,1)(2,1)(3,0)`) と `G2` (`(0,0)(1,1)(2,2)(3,0)`) が完成例である。
**まずこの 2 つを読むこと。** 以下は全部その反復。

#### 使えない道 (試さない)

`Evidence/Cert.lean` §21.2 が両方閉じている。

- **行の補題経由** — `Rows/` の事実は `Trans.o?` で証明されており、`o?` は撤回済み。
  `oR` との橋は無く、架けると既知の誤った関数を ✅ の依存に引き込む。
- **`++` に沿った帰納** — `runAux` の構造判定 (`fpar`・`adm`・`predP`) はリスト**全体**を見るので
  `p ++ q` の実行の中に `p` の実行が入らない。しかもメモ表を持ち回る。
  `Trans.oR_append` / `Recal.ofMatrix_append` は**構文解析の層だけ**で `runAux` には効かない。

使えるのは `runAux` 自身の再帰 `predP M = M.dropLast` に沿った帰納だけ。

#### 手順

0. **測る。証明の前に必ず。** 下を `#eval` で見て `#guard` に固定する。
   - `BMS.expand M n` の閉じた形 / `ofMatrix` の像 (= `L`) / `predP (L (m+1)) = L m`
   - `redP (L m) = L m`・`isPrincipalP`・`isZeroP`・`trMax`・`brF`・`firstNodes`・`joints`
   - `j0 = fpar M 0 j1 0`、`adm M j0`、`transTypeMain M j0 j1` (**型が何番か**)
   - `transPort (L m)` の像 (= `LBT`)
   - `Mark` の値 `((runAux (transFuel (L m)) (L m) (some (adm M j0))).run []).1`
     — **添字は `adm M j0` であって 1 とは限らない。G2 は 0 だった。**
   - `dict (LBT m)` が一致する `f`

1. **リンク 1** — `G1.expand_MG` / `all_len_rep` / `map_rep` / `ofMatrix_MG` をなぞる。軽い。

2. **`red` の燃料非依存性** — 一般定理は要らない。主枝が呼ぶ入力は 2〜3 個の**固定行列**で、
   片方は再帰が無く `rfl` で止まる (`G1.red_X1`/`red_X2`、`G2.red_Y1`/`red_Y2`)。

3. **`redP (L m) = L m`** — `runAux` の第 1 分岐を閉じる。主枝の畳み込みは**各段が同一**になるはず。
   要るもの: `len_L`・`lenI_L`・`gp0_L*`・`gp1_L*`・`fpar0_L*`・`fpar_L*`・`trMax_L`・
   `brF_L`・`firstNodes_L`・`joints_L`・`maxE_L`・`isPrincipalP_L`・畳み込みの閉じた形。

   **そのまま使える**: `G1.getD_repl`・`G1.getD_map_range`・`G1.foldl_congr_mem`・
   `G1.map_const_range`・`G1.dropLast_replicate`・`G1.beq_PS_self`・
   **`G2.ppair_repc`** (任意の定数列で `ppair (replicate m c) = replicate m [c]`)。

4. **一段ぶんの部品** — `adm_L`・`transType_L`・`mkC2_L`。
   `mkC2` は型で枝が変わる: 型 1/3/5 は `D v (bplus t2 (D (gp1 M j1) 0))`、型 2/4 は別、
   型 6 は `D v (D (gp1 M j1) 0)`。
   `Mark` の値が `Trans` と一致する行 (G2) は `G1.replMark_self` がそのまま効く。
   一致しない行 (G1) は `replMark_LG` にあたるものを別に要する。

5. **メモ帰納 → リンク 2** — `Sound` を回す。**表そのものを量化しない。**
   梯子の上で `runAux` が書き込む鍵は 3 種類だけ:
   `(L k, none)`・`(L k, some (adm M j0))`・底の `([(0,0)], none)`。
   `G1.Sound` / `G2.Sound2` と `_cons` / `_cons_base` をなぞる。`StateM` の do 記法は

   ```lean
   simp only [StateT.run, bind, StateT.bind, StateT.get, StateT.pure, pure,
     modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, get, getThe,
     MonadStateOf.get, Id.run, ...]
   ```

   で開く。`G1.run_hit`・`G1.run_base`・`G1.run_base_ok` は行に依らずそのまま使える。

6. **リンク 3** — **`collapse` は正規化器なので無条件の等式は無い。側条件を探すこと。**
   既にある法則:
   - `G1.collapse_one_mulOm` : `collapse 1 (Ω·m) = φ̄(0, Ω·(m+1))` — **m ≥ 1**
   - `G1.collapse_zero_pOm` : `collapse 0 (φ̄(0, Ω·j)) = φ̄(j,0)` — **j ≥ 2**
     (j = 1 が外れるのは `logOm` が [R91] 2.7 の不動点ずらしを踏むため)
   - `G2.collapse_zero_ZO` : `collapse 0 (Ω₂·(j+1)) = ψ_{Z0}(Ω₂·(j+1))` — **強臨界の枝**

   項の側は `Rows.ProofsB.fsN_phi_lim` で極限の層を剥がし、最内は `rw [fsN]`。
   `ψ` の節は `cofT` が `ω` なら素通り (G2)、そうでなければ対角化で**別の帰納が要る**。

7. **合流** — `oR = (1 + ·) ∘ dict ∘ transPort ∘ ofMatrix`。`1 +` は値が 1 より大きければ吸収。
   `G1.le_phiofNat_one` / `G2.le_psi_one` の形で `le <値> one = false` を出す。

### 残り 10 行と、その形 (測定済み)

**A. 1 列ずつ伸びる — 梯子がそのまま取れる。ここから始める。** (3 行)

```
(0,0)(1,1)(2,1)(3,0)(4,1)      ずらし 2   展開 = 先頭 4 列 ++ 昇り梯子 (4,0)(5,0)(6,0)…
(0,0)(1,1)(2,2)                ずらし無し 展開 = (0,0)(1,1) ++ 昇り梯子 (2,1)(3,1)(4,1)…
(0,0)(1,1)(2,2)(1,1)(2,2)      ずらし無し 展開 = 先頭 4 列 ++ 昇り梯子 (2,1)(3,1)(4,1)…
```

**G1・G2 と違うのは、足される列が一定でなく昇ること。** `zeroLad` (`Rows/Selected.lean` の
共通節) が同じ形の梯子で `decP_zeroLad`・`r0_zeroLad`・`inFrag_zeroLad` がある。
`red` の主枝と `ppair` は定数列の補題が効かないので取り直しになる。

**B. 2〜5 列ずつ伸びる — 梯子の細分が要る。** (7 行)

```
(0,0)(1,1)(2,2)(2,2)                     2 列ずつ (2,1)(3,2) / (3,1)(4,2) / …
(0,0)(1,1)(2,1)(3,1)           Γ₀        3 列ずつ 歩幅 3
(0,0)(1,1)(2,2)(3,1)           ずらし 0  3 列ずつ 歩幅 3
(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)           5 列ずつ 歩幅 1   (diff.md 族 4 の 326 行目)
(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)      ずらし 1  6 列ずつ (族 4 の 327)
(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)(2,1) ずらし 1  7 列ずつ (族 4 の 328)
(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)           5 列ずつ 歩幅 3
```

**`predP` は 1 対ずつしか降りないので、族がそのままでは再帰に乗らない。**
`Evidence/Cert.lean` §21.4 の `L` が答で、1 対ずつの梯子に細分して
`rungPS n = L (2n+1)` のように結ぶ。**そこを読んでから取りかかること。**

### $`f_n`$ が `fsN` に乗らない 6 行

上で「ずらし無し」の 6 行は、展開の値が `fsN t` の 0〜30 項のどこにも現れない。
**表の値が誤りという意味ではない。** ✅ が要求するのは $`f_n`$ が単調・有界・共終であることで、
標準基本列であることは要求していない。閉じた形は測ってあり、`Rows/Selected.lean` の
`fA`〜`fF` に定義と `#guard` がある。**その 6 行のリンク 3 の目標は `fA n` 等になる。**

---

## 3. ✅ への昇格 — 本丸

### 何を作るか (仕様)

**選定 23 行それぞれについて `CertifiedIn DomI M t` を証明し、`certRows` に登録する。**
書き足す場所は `lean/Evidence/Cert.lean` (または新しいファイルを作って `Cert.lean` から使う)。

```lean
-- (a) 土台。1 本ずつ独立に作れる
theorem cert_pad {M : Matrix} {t : Term} :
    CertifiedIn DomI M t → CertifiedIn DomI (M.map (fun c => c ++ [0])) t
    -- 2 行目が全部 0 の行列は BM4 の規則が無視する。導出への帰納 1 画面

theorem stdSeq_expand {s : List Nat} (h : Evidence.StageA.stdSeq s = true) (n : Nat) :
    Evidence.StageA.stdSeq (BMS.row0 (BMS.expand (Evidence.StageA.oneRow s) n)) = true
    -- 一行行列の族の再帰に再突入するのに要る。**未証明**

theorem certIn_oneRow {s : List Nat} (h : Evidence.StageA.stdSeq s = true) :
    CertifiedIn DomI (Evidence.StageA.oneRow s) (Evidence.StageA.oV s)
    -- Evidence.WF.acc_cn / wf_RCn 上の整礎再帰。展開の等式は StageA の e3_general の中にある

-- (b) 共終性を Veblen 断片へ。**ここが一番大きい**
theorem cof_fsCV : ∀ (t : Term), Evidence.WF.CNV t = true → <極限の条件> →
    ∀ s, inT s = true → lt s t = true → ∃ n, le s (Evidence.WF.fsC t n) = true
    -- 今ある cof_fsC は前提が `CN t` (CNF 断片) で、選定行の ζ₀ まわりに届かない

-- (c) 行ごと。23 行ぶん
theorem certIn_row_<name> : CertifiedIn DomI <その行の M> <その行の t>

-- (d) 登録。これを伸ばさないとビルドが落ちる (ゲート)
def certRows : List (Matrix × Term) := [... 既存 11 行 ..., <新しい行>...]
theorem certIn_rows_inT : ∀ p ∈ certRows, CertifiedIn DomI p.1 p.2

-- (e) 否定対照。行ごとに 1 本
theorem cert_row_<name>_not_<誤った値> :
    ¬ CertifiedIn DomI <その行の M> <誤った値>
    -- 例: ε₀ 行に ε₀·2 を認証しようとすると 𝔗(M) の本物の証人で潰れること
```

`CertifiedIn` の極限節が要求するのは 4 連言である。**2 で作る $`f_n`$ は第 1 連言の「値」を
与えるだけ**で、証明書ではない。

```
∀ n, CertifiedIn DomI (M[n]) (f n)   ← 展開そのものにも証明書が要る (再帰)
∀ n, f n < t
∀ n, f n < f (n+1)
∀ s ∈ 𝔗(M), s < t → ∃ n, s ≤ f n     ← 共終性。(b) がこれ
```

**素の `Certified` を作っても登録できない。** 忘却写像は `CertifiedIn → Certified` の
一方向だけである。

### 通すべきテスト

```lean
#eval Evidence.Cert.certRows.length                       -- 11 → 31 (既存 11 + 選定 23 のうち未登録 20)
#eval (Rows.Selected.selected.filter cert).length         -- 3 → 23
#print axioms Evidence.Cert.certIn_rows_inT               -- sorryAx 無し
```

```sh
leanman build                     # 0 errors。certRows を伸ばして証明を伸ばさないとここで落ちる
cd lean && lake exe gentable > ../table/table-r1.md
grep -c '✅\](' ../table/table-r1.md    # ✅ の数が増えていること
```

### 進め方

`Evidence/Cert.lean` の **Stage 2c 節** (`towerM` の定義の手前) に、ε₀ 行について
「残る前提は `∀ n, Certified (towerM n) (tower n)` の 1 本だけ」と、その中身が書いてある。
**まずそこを読む。** 順は

1. `cert_pad` — 独立。すぐ作れる
2. `stdSeq_expand` — 未証明。3 の前提
3. `certIn_oneRow` — 1・2 を使う
4. `fsN` と `fsC` の接続 — 測定では `fsC t n = fsN t (n+1)`。
   **あるいは `fsN` を捨てる** — `CertifiedIn.lim` は任意の `f` を取るので、
   `Evidence/WF.lean` §14 が `fsC` について 4 連言を直接与えている方を使ってよい
5. ε₀ 行が ✅ になる (1〜4 が揃うと出る)
6. **`cof_fsCV`** — ここを伸ばさないと選定行は 1 行も ✅ にならない。
   **3 に入ったら最初にこれを見積もること**
7. 行ごとの `certIn_row_*` と `certRows` の拡張
8. 否定対照。**これが無いと ✅ は「上限を確かめていない印」になる** (v0.1.41 の較正事故の教訓)

---

## 4. 外部の表との決着 — 族 4 の 3 行

### 何を作るか (仕様)

`table/diff.md` の族 4 (326〜328 行目) が未決。**当方が小で、構造が違う。**

```
325 (0,0)(1,1)(2,1)(2,1)(2,0)                = phi(1+1,w(0))     (一致)
326 先方 phi(1+1,phi(0,0))          oR phi(0,phi(1+1,w(0))+1)
327 先方 phi(1+1,phi(1,0))          oR phi(1,phi(1+1,w(0))+1)
328 先方 phi(1+1,phi(1+1,0))        oR phi(1+1,w(0)+1)
329 (0,0)(1,1)(2,1)(2,1)(2,1)                = phi(1+1+1,0)      (一致)
```

決着の付け方は族 1〜3 と同じで、`Rows.Selected.F3a` / `F3b` / `F3c` の `tHex` の節が手本である。
3 行それぞれについて `Rows/Selected.lean` に:

```lean
/-- 先方の値。先方の構文解析器で訳したもの -/
def tHex : Term := <訳した項>
```

先方の値の訳し方:

```sh
python3 -c "
import importlib.util
spec=importlib.util.spec_from_file_location('h','scripts/hexirp-rathjen-check.py')
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
print(m.to_lean(m.parse_term('phi(1+1,phi(0,0))')))
"
```

### 通すべきテスト

```lean
#guard !(Trans.oR M == some tHex)                            -- 値が違う
#guard kindT tHex == KindT.isLim                             -- 比べる意味がある形
#guard (List.range 6).all fun k => (List.range 8).any fun n =>
  !(Trans.oR (BMS.expand M n) == some (fsN tHex (n + k)))    -- どのずらしでも乗らない
#guard (List.range 4).all fun n => (List.range 30).all fun j =>
  !(Trans.oR (BMS.expand M n) == some (fsN tHex j))          -- 30 項まで現れない
-- CTRL 同じ探索を当方の値に当てると当たる
#guard (List.range 4).all fun n => (List.range 30).any fun j =>
  Trans.oR (BMS.expand M n) == some (fsN t j)
```

**前提**: その 3 行の $`f_n`$ が 2 で定理になっていること (3 行とも「B. 2〜5 列ずつ」に入っている)。

文書側:

- `table/diff.md` の族 4 の見出しを**大小ではなく勝敗で**書き直す (「未決。当方が小」→「当方が正しい。証明済み」)
- 冒頭の集計 (「6 行は証明で決着した。残る 3 行は未決」) を更新
- `lean/Rows/TM.lean` のその 3 行の `note` を「外部の表と食い違うが決着済み。当方が正しい」に
- 表を再生成

---

## 5. 付随 3 件

**✅ には効かない。** 独立に片付けられる。

### 5.1 `dictInv` の標準形 5 行

`lean/Trans/DictInv.lean` の `dictInv : Term → Option BT` は表 60 行で 60 rt / 0 none だが、
**5 行が非標準の Buchholz 項を返す** (diff.md の族 2・3 に当たる行)。

- **作るもの**: 非標準になる 5 行を特定する `#guard` と、どこで非標準が出るかの記録
- **テスト**: `#guard (rows.filter fun r => (dictInv r.t).isSome && !(isStd ...)).length == 5`
  のような形で数を固定し、原因をコメントに書く
- 値が誤りという話ではない (`dict` を通すと正しい 𝔗(M) の項に戻る)。
  `dictInv` を「順序同型の逆」として使うなら塞ぐ必要がある、というだけ

### 5.2 [R91] 2.7 の食い違い

`lean/TM/FS.lean` の `phiShifted` は [R91] 2.7 の逐語転記で、第 2 選言が `b == zero && a.isSC`。
**そのままだと φ̄α0 と φ̄α1 が同じ順序数に潰れる**が、2.8 の F は順序を保つと言っていて両立しない。
独立の証拠 (naruyoko 氏の実装との突き合わせ) では `isFP a (splitFin b).1 || a.isSC` が
742/742 で合う (逐語版は 734/742)。

- **作るもの**: (a) どちらが [R91] の意図かを本文から決める、(b) 変えるなら `fsN` と
  StageB/ProofsB の約 60 の補題を全部通し直す、(c) 変えないならその理由を `phiShifted` の
  docstring に追記
- **テスト**: `leanman build` が 0 errors のまま。**変えると E3 が全部落ちるので、
  落ちた数を数えてから決めること**

### 5.3 `Classical.choice`

`lean/scripts/axiom_sweep.lean` の台帳に、`Classical.choice` を持つ宣言の数の推移がある
(236 → 239 → 241 → 249)。増分は全部 `Evidence/StageB.lean` の
`oLV_eq` / `oLAux_eq_oLV` / `blocksP_append` からの継承。

- **作るもの**: `StageB` の `foldl_congrP` まわりを choice-free に書き直す
- **テスト**: `leanman check -C <repo>/lean --backend lean lean/scripts/axiom_sweep.lean` が
  exit 0 で、台帳の数が減っていること
- 優先度は低い。ただし**台帳の数は毎回更新すること**


---

## 付録 A: 過去に踏んだ穴

**この作業で既に 4 回、読みで書いて外している。測ってから書くこと。**

| 外した読み | 実際 |
|---|---|
| F3a は深さが n とともに増える | 4 段で平坦な連鎖になる |
| `Mark` の添字は 1 | 行による。G2 は 0 (`adm M j0` を測ること) |
| `ppair` の補題は列ごとに要る | 任意の定数列で成り立つ (`G2.ppair_repc`) |
| `red` の燃料非依存性は一般定理が要る | 主枝が呼ぶ入力は 2〜3 個の固定行列だけ |

**外部の表と食い違ったら、自分の翻訳を先に疑う。** 過去に 3 回、翻訳の誤りを外部の誤りと報告している。

### `Classical.choice` が入ったときの直し方

このリポジトリの定理は `[propext, Quot.sound]` 以下で通っている。増えたら**戦術由来**を疑う。
4 回あって 4 回とも主張を変えずに消せた。

| 原因 | 直し方 |
|---|---|
| `omega` を非算術の目標に当てる | `rw [if_neg (by omega), ...]` に分け、`omega` は算術の部分目標だけに |
| `simp only [beq_self_eq_true, if_true]` を `if` に当てる | `rw [if_pos (by rfl)]` |
| `simp` を Bool の目標に当てる | 明示の `rw` に置き換える |
| `beq_self_eq_true` を使う | 手で書く。`Int` は `decide_eq_true rfl`、`Prod`・`List`・`BT` は構造帰納 (`G1.beq_Int_self` 等が既にある) |

## 付録 B: 記録の仕方

- 測定は `#guard` でリポジトリに固定する。**対照 (CTRL) も置く** —
  「添字を 1 ずらすと壊れる」など、偶然の一致でないことを示すもの。
- 進んだら [table/diff.md](table/diff.md) の作業ツリーの葉を `🚨` → `✅` にし、所見は本文にも書く。
  `🚨🤖` は着手中の葉に 1 つだけ。
- **表 `table/table-r1.md` は生成物。手で編集しない。**
  `lean/Rows/TM.lean` を直して `cd lean && lake exe gentable > ../table/table-r1.md`。
  `Rows.version` も上げる。
- `.md` を触ったら `node scripts/check-math.js <file>...` を通す (0 errors)。
- **これ (step.md) は作業ファイルであって公開文書ではない。** 公開文書は README.md・
  table/table-r1.md・table/diff.md の 3 つで、そちらはローカルパスを書かない・
  数式は GitHub の MathJax、という規則に従う。

## 付録 C: よく使う場所

| 何 | どこ |
|---|---|
| 選定行の証明 | `lean/Rows/Selected.lean` (G1・G2 が `oR` 側の完成例) |
| 行データベース | `lean/Rows/TM.lean` (`rows`、`version`、`gentable` の本体) |
| 証明書 | `lean/Evidence/Cert.lean` (§21 が `oR` 側の先行例、Stage 2c が ✅ 昇格の設計) |
| 𝔗(M) の順序・整礎性 | `lean/Evidence/WF.lean` (§14 が共終性) |
| 2 行断片の値 | `lean/Evidence/StageB.lean` (`oLV`・`oLAux_chainR`) |
| 読み手 | `lean/Trans/Recal.lean` (`runAux`・`red`・`ppair`)、`lean/Trans/Dict.lean` (`collapse`・`dict`) |
| 基本列 | `lean/TM/FS.lean` (`fsN`・`phiShifted`) |
| 作業原則 | `plan/constitutions.md` |
| 設計と撤回の記録 | `plan/README.md` |
