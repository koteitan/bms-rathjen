# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.7.13

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
| [`(空)`](../lean/Rows/TM.lean#L116) | $`0`$ | $`0`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L44)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L118) | $`1`$ | $`1`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L57)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L119) | $`2`$ | $`2`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L70)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L120) | $`\omega`$ | $`\omega`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L83)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L123) | $`\omega+\omega`$ | $`\omega\cdot 2`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L96)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L125) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L109)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L127) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L122)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L129) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L135)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\varepsilon_0`$ |  | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) について、展開の値を一般定理で一括証明 |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L132) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L343)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| [`(0,0)(1,1)(0,0)`](../lean/Rows/TM.lean#L135) | $`\bar{\varphi}(1,0)+1`$ | $`\varepsilon_0+1`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L152)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L137) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L189)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L140) | $`\bar{\varphi}(1,1)`$ | $`\varepsilon_1`$ |  | [fₙ](../lean/Rows/Proofs.lean#L345)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L142) | $`\bar{\varphi}(1,\omega)`$ | $`\varepsilon_\omega`$ |  | [fₙ](../lean/Rows/Proofs.lean#L346)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(0,0)`](../lean/Rows/TM.lean#L145) | $`\bar{\varphi}(1,\omega)+1`$ | $`\varepsilon_\omega+1`$ |  | [fₙ](../lean/Rows/Proofs.lean#L269)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(1,1)(1,0)(2,1)(3,0)(1,0)(2,1)`](../lean/Rows/TM.lean#L148) | $`\bar{\varphi}(0,\bar{\varphi}(1,\omega+1)+\bar{\varphi}(1,\omega)+\bar{\varphi}(1,0))`$ | $`\bar{\varphi}(0,\bar{\varphi}(1,\omega+1)+\bar{\varphi}(1,\omega)+\bar{\varphi}(1,0))`$ |  | [fₙ](../lean/Rows/Selected.lean#L312) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 1) |
| [`(0,0)(1,1)(2,0)(2,0)`](../lean/Rows/TM.lean#L154) | $`\bar{\varphi}(1,\bar{\varphi}(0,2))`$ | $`\varepsilon_{\omega^2}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L299)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,0)`](../lean/Rows/TM.lean#L156) | $`\bar{\varphi}(1,\bar{\varphi}(0,\omega))`$ | $`\varepsilon_{\omega^\omega}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L284)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L159) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\varepsilon_{\varepsilon_0}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L252)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L161) | $`\bar{\varphi}(2,0)`$ | $`\zeta_0`$ |  | [fₙ](../lean/Rows/Proofs.lean#L348)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(0,0)`](../lean/Rows/TM.lean#L164) | $`\bar{\varphi}(2,0)+1`$ | $`\zeta_0+1`$ |  | [fₙ](../lean/Rows/Proofs.lean#L164)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,0)`](../lean/Rows/TM.lean#L166) | $`\bar{\varphi}(0,\bar{\varphi}(2,0))`$ | $`\omega^{\zeta_0+1}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L191)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,1)`](../lean/Rows/TM.lean#L168) | $`\bar{\varphi}(1,\bar{\varphi}(2,0))`$ | $`\varepsilon_{\zeta_0+1}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L234)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(1,1)(2,0)`](../lean/Rows/TM.lean#L172) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\omega)`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\omega)`$ |  | [fₙ](../lean/Rows/Selected.lean#L573) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 2) |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L178) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\bar{\varphi}(1,0))`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\bar{\varphi}(1,0))`$ |  | [fₙ](../lean/Rows/Selected.lean#L843) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 2) |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)`](../lean/Rows/TM.lean#L185) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)))))`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)))))`$ |  | [fₙ](../lean/Rows/Selected.lean#L1046) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3) |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)(6,1)`](../lean/Rows/TM.lean#L191) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(1,0)))))`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(1,0)))))`$ |  | [fₙ](../lean/Rows/Selected.lean#L1348) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3) |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)(6,1)(7,1)`](../lean/Rows/TM.lean#L197) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(2,0)))))`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(2,0)))))`$ |  | [fₙ](../lean/Rows/Selected.lean#L1685) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3) |
| [`(0,0)(1,1)(2,1)(2,0)`](../lean/Rows/TM.lean#L209) | $`\bar{\varphi}(2,\omega)`$ | $`\zeta_\omega`$ |  |  | 旧値 ε_{ζ₀·ω} を訂正 (較正事故) |
| [`(0,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L212) | $`\bar{\varphi}(3,0)`$ | $`\bar{\varphi}(3,0)`$ |  |  | 旧値 ζ₁ を訂正 (較正事故の初検出行) |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)`](../lean/Rows/TM.lean#L216) | $`\bar{\varphi}(1,\bar{\varphi}(3,\omega))`$ | $`\bar{\varphi}(1,\bar{\varphi}(3,\omega))`$ |  | [fₙ](../lean/Rows/G9.lean#L6) | 外部の表と食い違う ([diff.md](diff.md) 族 4) |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L222) | $`\bar{\varphi}(2,\bar{\varphi}(3,\omega))`$ | $`\bar{\varphi}(2,\bar{\varphi}(3,\omega))`$ |  | [fₙ](../lean/Rows/G10.lean#L6) | 外部の表と食い違う ([diff.md](diff.md) 族 4) |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L229) | $`\bar{\varphi}(3,\omega+1)`$ | $`\bar{\varphi}(3,\omega+1)`$ |  |  | 外部の表と食い違う ([diff.md](diff.md) 族 4) |
| [`(0,0)(1,1)(2,1)(3,0)`](../lean/Rows/TM.lean#L235) | $`\bar{\varphi}(\omega,0)`$ | $`\bar{\varphi}(\omega,0)`$ |  | [fₙ](../lean/Rows/Selected.lean#L2114) | 旧値 ζ_ω を訂正 |
| [`(0,0)(1,1)(2,1)(3,0)(4,1)`](../lean/Rows/TM.lean#L239) | $`\bar{\varphi}(\bar{\varphi}(1,0),0)`$ | $`\bar{\varphi}(\varepsilon_0,0)`$ |  | [fₙ](../lean/Rows/G3.lean#L6) | 旧値 ζ_{ε₀} を訂正 |
| [`(0,0)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L243) | $`\psi_{\Omega}(0)`$ | $`\Gamma_0`$ |  | [fₙ](../lean/Rows/G7.lean#L6) | ψ 項の初登場。旧値 φ̄(3,0) を訂正 |
| [`(0,0)(1,1)(2,1)(3,1)(0,0)`](../lean/Rows/TM.lean#L247) | $`\psi_{\Omega}(0)+1`$ | $`\Gamma_0+1`$ |  |  |  |
| [`(0,0)(1,1)(2,1)(3,1)(1,0)`](../lean/Rows/TM.lean#L249) | $`\bar{\varphi}(0,\psi_{\Omega}(0))`$ | $`\omega^{\Gamma_0+1}`$ |  |  |  |
| [`(0,0)(1,1)(2,2)`](../lean/Rows/TM.lean#L261) | $`\psi_{\Omega}(Z(1))`$ | $`\psi_{0}(\psi_{2}(0))`$ |  | [fₙ](../lean/Rows/G4.lean#L6) | 行 1 に 2 が現れる最初の行。旧値 φ̄(ω,0) を訂正 |
| [`(0,0)(1,1)(2,2)(1,1)`](../lean/Rows/TM.lean#L265) | $`\bar{\varphi}(1,\psi_{\Omega}(Z(1)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(0))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)`](../lean/Rows/TM.lean#L268) | $`\bar{\varphi}(2,\psi_{\Omega}(Z(1)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{1}(0)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L271) | $`\psi_{\Omega}(Z(1)+1)`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{1}(\psi_{1}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L275) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)))`$ |  | [fₙ](../lean/Rows/G5.lean#L7) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L279) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0))+\psi_{1}(\psi_{2}(0)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)`](../lean/Rows/TM.lean#L283) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(0)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(2,0)`](../lean/Rows/TM.lean#L287) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+1))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(0)+\psi_{0}(0)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,0)`](../lean/Rows/TM.lean#L291) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(\psi_{0}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)`](../lean/Rows/TM.lean#L295) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,0)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(\psi_{1}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)(4,2)`](../lean/Rows/TM.lean#L299) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\psi_{\Omega}(Z(1))))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(\psi_{2}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,1)`](../lean/Rows/TM.lean#L304) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{1}(0)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(2,1)`](../lean/Rows/TM.lean#L308) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega+\Omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{1}(0)+\psi_{1}(0)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,1)`](../lean/Rows/TM.lean#L312) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(0,\Omega+\Omega)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{1}(\psi_{1}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,2)`](../lean/Rows/TM.lean#L317) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,2)`](../lean/Rows/TM.lean#L322) | $`\psi_{\Omega}(Z(1)+Z(1))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{2}(0))`$ |  | [fₙ](../lean/Rows/G6.lean#L6) | 旧値 φ̄(ω²,0) を訂正 |
| [`(0,0)(1,1)(2,2)(2,2)(2,2)`](../lean/Rows/TM.lean#L327) | $`\psi_{\Omega}(Z(1)+Z(1)+Z(1))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{2}(0)+\psi_{2}(0))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,0)`](../lean/Rows/TM.lean#L331) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(0)))`$ |  | [fₙ](../lean/Rows/Selected.lean#L3557) | 旧値 φ̄(ω^ω,0) を訂正 |
| [`(0,0)(1,1)(2,2)(3,0)(3,0)`](../lean/Rows/TM.lean#L336) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+1))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(0)+\psi_{0}(0)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,0)`](../lean/Rows/TM.lean#L339) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\omega))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(\psi_{0}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)`](../lean/Rows/TM.lean#L342) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\bar{\varphi}(1,0)))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(\psi_{1}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)`](../lean/Rows/TM.lean#L345) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\psi_{\Omega}(Z(1))))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(\psi_{2}(0))))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,1)`](../lean/Rows/TM.lean#L349) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\Omega))`$ | $`\psi_{0}(\psi_{2}(\psi_{1}(0)))`$ |  | [fₙ](../lean/Rows/G8.lean#L6) |  |

# 証明の仕様

対応表の 1 行 $`(M, t)`$ について、**証明列に ✅ が付く条件はこれだけ**である。
ほかの列は ✅ の材料か、材料ですらない参考値である。

- 命題 — [E.cert](#ecert) · [E.zero](#ezero) · [E.succ](#esucc) · [E.lim](#elim) · [E.fs](#efs)
- 定義 — [D.TM](#dtm) · [D.expand](#dexpand)
- 定理 — [T.unique](#tunique) · [T.bound](#tbound) · [T.eps0](#teps0)

## E.cert

```math
\mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;t
```

読み下すと、次の 2 つを同時に満たすことである。

1. 下の 3 規則 E.zero / E.succ / E.lim で $`(M,t)`$ の導出が組める。
   使う規則は行の種別 $`\mathrm{kind}\,M`$ (空・後続・極限) が決めるので、
   1 行につきどれか 1 つだけである
2. **その導出に現れる値が、1 つ残らず $`\mathfrak{T}(M)`$ の項である**
   ($`\mathrm{DomI}(t) :\equiv t \in \mathfrak{T}(M)`$ が全ノードに掛かる)

**2 を落とすと値が決まらない。** 3 規則だけを規則とする帰納的述語
($`\mathrm{Certified}`$) は認証する値に何の制約も課さないので、
$`\mathfrak{T}(M)`$ の項でない値も通ってしまう:

```math
\mathrm{Certified}\;[(0)(1)]\;\omega
\qquad\text{かつ}\qquad
\mathrm{Certified}\;[(0)(1)]\;(1+M)
```

$`1+M`$ は $`\mathfrak{T}(M)`$ の項ではない — 和は降順でなければならない
([D.TM](#dtm)) — ので、2 がこれを弾く。

**素の $`\mathrm{Certified}`$ を証明しても ✅ は付かない。** 写像は

```math
\mathrm{CertifiedIn}\;\mathrm{Dom} \;\longrightarrow\; \mathrm{Certified}
```

の**弱める向きだけ**で、逆は無いからである。

**E.cert は表の登録ゲートでもある。** レジストリに行を足すにはこの導出が要り、
証明を足さずに一覧だけ伸ばすとビルドが落ちる。

## E.zero

空行列の行。前提は無い。

```math
\mathrm{Certified}\;[\,]\;0
```

## E.succ

```math
\begin{aligned}
&\mathrm{kind}\,M = \mathrm{succ} \;\Longrightarrow \cr
&\quad \Bigl[\; \mathrm{Certified}\;M\;u \;\Longleftrightarrow\;
   \exists t.\; u = t+1 \;\land\; \forall n.\;\mathrm{Certified}\;(M[n])\;t \;\Bigr]
\end{aligned}
```

すべての展開が同じ $`t`$ を認証するなら、この行は $`t+1`$ である。

## E.lim

```math
\begin{aligned}
&\mathrm{kind}\,M = \mathrm{lim} \;\Longrightarrow \cr
&\quad \Bigl[\; \mathrm{Certified}\;M\;t \;\Longleftrightarrow\;
   \exists f : \mathbb{N} \to \mathfrak{T}(M).\; \cr
&\qquad\qquad\quad \forall n.\;\mathrm{Certified}\;(M[n])\;(f_n) \cr
&\qquad\qquad\quad \land\; \forall n.\;f_n < t \cr
&\qquad\qquad\quad \land\; \forall n.\;f_n < f_{n+1} \cr
&\qquad\qquad\quad \land\; \forall s \in \mathfrak{T}(M).\;s < t \to \exists n.\;s \le f_n \;\Bigr]
\end{aligned}
```

**$`f`$ はどこにも定義されていない。** $`\exists`$ で束縛された列であり、行ごとに
証明が 1 つ選んで与える。表を読むときに $`f`$ の定義を探す必要は無い。

**選べるのは見かけだけである。** 4 連言のうち $`f_n`$ が何であるかを言うのは第 1 のもの
だけで、残る 3 つは「$`t`$ 未満」「増加」「$`t`$ に共終」という**性質**にすぎない。
性質は列を 1 つに絞らない — $`\varepsilon_1`$ の行で 3 つの候補が 3 つとも 3 性質を
満たし、正しい列はそのどれでもなかった
([plan/constitutions.md](../plan/constitutions.md) C2)。

決めるのは第 1 連言である。$`f_n`$ は $`M[n]`$ が認証した値**そのもの**でなければ
ならないので、$`f`$ を選んでいるのは行列であって $`\mathfrak{T}(M)`$ 側の都合ではない。
だから $`f`$ が $`\mathfrak{T}(M)`$ の標準基本列と一致する必要はどこにも無い。

## E.fs

弱いエビデンスの $`f_n`$ 印の中身。**E.lim の第 1 連言の「値の側」だけ**を言う。

```math
\forall n.\; r\,(M[n]) = \mathrm{fsN}\;t\;k(n)
```

$`r`$ は読み手で、行によって `o?` か `oR` である (両方が定義される所では一致する)。
$`\mathrm{fsN}\,t`$ は $`\mathfrak{T}(M)`$ 側の基本列、$`k`$ はその行の添字で
**行ごとに違う** (一律に $`n+1`$ ではない)。有限個の $`n`$ を試したのではなく、
すべての $`n`$ についての定理である。

**$`M[n]`$ がその値を認証することは言っていない。** 第 1 連言が要求するのは後者であり、
残る 3 連言は手つかずである。E.fs は E.cert の材料の一部であって、E.cert に近いことを
意味しない。

## E.cert が言っていないこと

E.lim の第 4 連言は $`f`$ が $`t`$ に共終だと言っており、第 2・第 3 連言と合わせて
$`\sup_n f_n = t`$ が出る。$`\mathfrak{T}(M)`$ 側の共終性は証明の中にある。

言っていないのは BMS 側である:

```math
\sup_n |M[n]| = |M|
```

これが無いと $`\sup_n f_n = t`$ から $`|M| = t`$ へ渡れない。そしてこのリポジトリに
$`|M[n]| \lt |M|`$ も展開列の共終性も**補題として存在しない**。BMS を順序数表記として
読むとき極限行の値が展開の上限であることは**読み方の定義**であって定理ではないからである。
E.cert はこの読み方を仮定した上で $`\mathfrak{T}(M)`$ 側を尽くしている。

# 定義

## D.TM

$`M`$ は最小の弱 Mahlo 基数。$`\mathfrak{T}(M)`$ は**次の規則で閉じた最小の項集合**
(Rathjen 1991 §2.1):

```math
\frac{}{0 \in \mathfrak{T}(M)}
\qquad
\frac{}{M \in \mathfrak{T}(M)}
\qquad
\frac{\alpha \in \mathfrak{T}(M) \quad M < \alpha}
{\bar\omega^{\alpha} \in \mathfrak{T}(M)}
\qquad
\frac{\alpha \in \mathfrak{T}(M)}{Z(\alpha) \in \mathfrak{T}(M)}
```

```math
\frac{\alpha, \beta \in \mathfrak{T}(M) \quad \alpha, \beta < M}
{\bar\varphi(\alpha, \beta) \in \mathfrak{T}(M)}
\qquad
\frac{\kappa, \alpha \in \mathfrak{T}(M) \quad \kappa \in R
\quad \alpha < M \quad K_\kappa \alpha < \alpha}
{\psi_\kappa(\alpha) \in \mathfrak{T}(M)}
```

```math
\frac{\alpha_1, \dots, \alpha_n \in AP \quad n \ge 2
\quad \alpha_n \le \dots \le \alpha_1}
{\alpha_1 \oplus \dots \oplus \alpha_n \in \mathfrak{T}(M)}
```

$`AP`$ は加法的主要、$`SC`$ は強クリティカル、$`R`$ は正則:

```math
AP = \{M\} \cup \{\bar\omega^\alpha\} \cup \{\bar\varphi(\alpha,\beta)\} \cup SC,
\qquad
SC = \{M\} \cup \{\psi_\kappa\alpha\} \cup \{Z\alpha\},
\qquad
R = \{Z\alpha\}
```

$`\oplus`$ の条件 (成分が $`AP`$、降順) が一意な正規形を与える。

**$`\bar\varphi`$ は $`\omega^\cdot`$ の不動点を飛ばして数える** ([R91] 2.6(vi))。
$`\bar\varphi(0,\beta)`$ は最初の不動点未満では $`\omega^\beta`$ だが、

```math
\bar\varphi(0, \varepsilon_0) = \omega^{\varepsilon_0 + 1} \ne \varepsilon_0
```

**不動点の下では 2 つの読みが一致するので、そこだけで較正した関数・コーパス・読者は
上で静かに誤る。**

## D.expand

$`M[n]`$ は行列 $`M`$ の $`n`$ 番目の展開 (BM4 の規則)。$`\mathrm{kind}\,M`$ は
行が空か・後続か・極限かを言う。定義は [BMS/Expand.lean](../lean/BMS/Expand.lean)。

# 定理

E.cert が証明された行について、追加で言えること。

## T.unique

導出に現れる値がすべて $`\mathfrak{T}(M)`$ の項である範囲では、この行は $`t`$ 以外の
値を取り得ない。上下いずれの側も排除されている。

```math
\forall u.\;\;\mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;u \;\Longrightarrow\; u = t
```

## T.bound

値が $`\mathfrak{T}(M)`$ の外に出るものも含め、いかなる証明書も $`\omega^{t+1}`$ 以上を
与えない。$`\mathrm{DomI}`$ の仮定が無いことに注意。

```math
\forall u.\;\;\mathrm{Certified}\;M\;u \;\Longrightarrow\; \bar\varphi(0,\,t+1) \not\le u
```

## T.eps0

$`\varepsilon_0`$ の行では、その直上から塞がれている。

```math
\forall u.\;\; \varepsilon_0 < u \;\Longrightarrow\;
\neg\,\mathrm{Certified}\;[(0,0)(1,1)]\;u
```

**まだ排除できていないのは片側だけである** — $`t`$ より**下**の値が、
$`\mathfrak{T}(M)`$ の外へ出る部分値を経由して認証される可能性。上側は T.bound が
無条件に塞いでいる。

# その他の弱いエビデンス

いずれも ✅ の材料であって ✅ ではない。$`f_n`$ 以外は有限個の計算検査であり、
較正誤りを検出できない。

| 記号 | 意味 | 全ての $`n`$? |
|---|---|---|
| $`f_n`$ | [E.fs](#efs) が Lean の定理 | はい |
| `o` | 翻訳関数がこの行列で定義され $`o(M) = t`$ (両辺を同じ写像で計算するので較正誤りは検出できない) | いいえ |
| `bisim6` | 深さ 6 の双模倣 | いいえ |
| `checkAll` | 区間の全標準行列についての一般定理 | はい (区間全体) |

**印はビルドが計算する。** ✅ は証明書レジストリから、$`f_n`$ は行が指す名前空間を
証明ファイルから探して付ける。名前空間を消したり改名したりすると印そのものが消えるので、
実体の無い印は残らない。

# 値についての注意

**$`\psi_\Omega(Z(1))`$ 以上の行の値は外部資料と食い違っており、まだ決着していない。**
BMS `(0,0)(1,1)(2,2)` の Buchholz 値 $`\psi_0(\psi_2(0))`$ には 3 者が一致するが、
そこから $`\mathfrak{T}(M)`$ へ訳す段で割れる:

```math
\text{当方} \;\longmapsto\; \psi_\Omega(Z(1)) \qquad
\text{資料} \;\longmapsto\; \psi_\Omega(\bar\varphi(1, \Omega+1))
```

**根は型にある。** このリポジトリは $`\chi`$ を $`Z\,a = \chi_a(0)`$ と 1 引数に潰して
いるが、原典の $`\chi`$ は 2 引数で第 2 引数が $`\Omega`$ 階層を枚挙する
($`\chi_0(\alpha) = \Omega_{1+\alpha}`$、$`\chi_1(0) = I`$)。つまり $`Z\,1`$ は
$`\Omega_2`$ ではなく $`I`$ で、$`\Omega_2 = \chi_0(1)`$ は現在の型では書けない。
直すには項型を変える必要がある。

**✅ の付いた行は影響を受けない。** ✅ は $`\mathrm{Certified}`$ から来ており、
翻訳関数を一度も通らないからである。

外部の対応表との差分は [diff.md](diff.md) に、再実行手順は
[scripts/external-check.py](../scripts/external-check.py) にある。

# 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean) ·
[証明書](../lean/Evidence/Cert.lean)
