# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.1.56

> **⚠ 較正事故の記録 (v0.1.41–v0.1.48)**: 旧翻訳 $`o`$ は
> `(0,0)(1,1)(2,1)(2,0)` 以上で系統的に誤った値を与えていた
> (旧 ✅ 付き行を含む。経緯は [plan/README.md](../plan/README.md) の
> 「較正事故」節)。現在の表の全行は、P進大好きbot 氏のペア数列停止性証明の
> 変換写像 (の Lean 移植 oR) と一致することが**ビルド時 #guard で強制**されている。
> 証明列 (✅) は意味証明書 (SemanticCert) の存在する行のみに機械付与され、
> oR 由来の値は**予想ティア** (オラクル較正済み・意味論の証明は未了) である。

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`T(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応表。検査の設計は
[plan/README.md](../plan/README.md) を参照。

エビデンス凡例:

- **証明列**: ✅ = [意味証明書](../lean/Evidence/Cert.lean) `Certified M t`
  (行列の値が t であることの、展開閉包全体を含む閉じた帰納) が Lean に存在する行。
  ビルドが証明書レジストリから機械的に付与し、手で宣言することはできない。
  旧来の「o?-値についての定理」ベースの ✅ は較正事故により撤去した (警告参照)。
- **その他の弱いエビデンス** (いずれも有限個の $`n`$ の計算検査であり、
  **較正誤りを検出できない**ことが今回実証された):
  - $`o`$ = 翻訳関数がこの行列で定義され $`o(M) = t`$ が成立 (E1)。
  - oR = オラクル較正済み候補値: P進大好きbot 氏のペア数列停止性証明の
    変換写像の Lean 移植 (oR = dict∘TransPort) の値と一致 (予想ティア)。
    全行が oR と一致することはビルド時 #guard で強制される。
  - bisim6 = 深さ 6 の双模倣 (展開列と基本列が一致する領域で有効)。
  - oStageC = Stage C の候補翻訳 oStageC? の値の一致。

## 対応表

| BMS | $`T(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L86) | $`0`$ | $`0`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L88) | $`1`$ | $`1`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L89) | $`2`$ | $`2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L90) | $`\omega`$ | $`\omega`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L92) | $`\omega+\omega`$ | $`\omega\cdot 2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L94) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L96) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L98) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\varepsilon_0`$ |  | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明 |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L101) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| [`(0,0)(1,1)(0,0)`](../lean/Rows/TM.lean#L103) | $`\bar{\varphi}(1,0)+1`$ | $`\varepsilon_0+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L105) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ |  | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L107) | $`\bar{\varphi}(1,1)`$ | $`\varepsilon_1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L109) | $`\bar{\varphi}(1,\omega)`$ | $`\varepsilon_\omega`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(0,0)`](../lean/Rows/TM.lean#L111) | $`\bar{\varphi}(1,\omega)+1`$ | $`\varepsilon_\omega+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(2,0)`](../lean/Rows/TM.lean#L113) | $`\bar{\varphi}(1,\bar{\varphi}(0,2))`$ | $`\varepsilon_{\omega^2}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,0)`](../lean/Rows/TM.lean#L115) | $`\bar{\varphi}(1,\bar{\varphi}(0,\omega))`$ | $`\varepsilon_{\omega^\omega}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L118) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\varepsilon_{\varepsilon_0}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L120) | $`\bar{\varphi}(2,0)`$ | $`\zeta_0`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(0,0)`](../lean/Rows/TM.lean#L122) | $`\bar{\varphi}(2,0)+1`$ | $`\zeta_0+1`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,0)`](../lean/Rows/TM.lean#L124) | $`\bar{\varphi}(0,\bar{\varphi}(2,0))`$ | $`\omega^{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,1)`](../lean/Rows/TM.lean#L126) | $`\bar{\varphi}(1,\bar{\varphi}(2,0))`$ | $`\varepsilon_{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(2,0)`](../lean/Rows/TM.lean#L133) | $`\bar{\varphi}(2,\omega)`$ | $`\zeta_\omega`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ε_{ζ₀·ω} を訂正 (較正事故) |
| [`(0,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L136) | $`\bar{\varphi}(3,0)`$ | $`\bar{\varphi}(3,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ₁ を訂正 (較正事故の初検出行) |
| [`(0,0)(1,1)(2,1)(3,0)`](../lean/Rows/TM.lean#L139) | $`\bar{\varphi}(\omega,0)`$ | $`\bar{\varphi}(\omega,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ_ω を訂正 |
| [`(0,0)(1,1)(2,1)(3,0)(4,1)`](../lean/Rows/TM.lean#L141) | $`\bar{\varphi}(\bar{\varphi}(1,0),0)`$ | $`\bar{\varphi}(\varepsilon_0,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ_{ε₀} を訂正 |
| [`(0,0)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L143) | $`\psi_{\Omega}(0)`$ | $`\Gamma_0`$ |  | [oR](../lean/Trans/Recal.lean) | ψ 項の初登場。旧値 φ̄(3,0) を訂正 |
| [`(0,0)(1,1)(2,1)(3,1)(0,0)`](../lean/Rows/TM.lean#L146) | $`\psi_{\Omega}(0)+1`$ | $`\Gamma_0+1`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,1)(3,1)(1,0)`](../lean/Rows/TM.lean#L148) | $`\bar{\varphi}(0,\psi_{\Omega}(0))`$ | $`\omega^{\Gamma_0+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,1)(3,2)`](../lean/Rows/TM.lean#L150) | $`\psi_{\Omega}(\bar{\varphi}(1,\Omega))`$ | $`\psi_0(\varepsilon_{\Omega+1})`$ |  | [oR](../lean/Trans/Recal.lean) | Bachmann–Howard 順序数 |
| [`(0,0)(1,1)(2,2)`](../lean/Rows/TM.lean#L153) | $`\psi_{\Omega}(Z(1))`$ | $`\psi_0(\Omega_2)`$ |  | [oR](../lean/Trans/Recal.lean) | 行 1 に 2 が現れる最初の行。旧値 φ̄(ω,0) を訂正 |
| [`(0,0)(1,1)(2,2)(1,1)`](../lean/Rows/TM.lean#L156) | $`\bar{\varphi}(1,\psi_{\Omega}(Z(1)))`$ | $`\varepsilon_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)`](../lean/Rows/TM.lean#L159) | $`\bar{\varphi}(2,\psi_{\Omega}(Z(1)))`$ | $`\zeta_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L162) | $`\psi_{\Omega}(Z(1)+1)`$ | $`\Gamma_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L165) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L168) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2)\cdot 2)`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)`](../lean/Rows/TM.lean#L172) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+1))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(2,0)`](../lean/Rows/TM.lean#L176) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+1))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,0)`](../lean/Rows/TM.lean#L180) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\omega))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)`](../lean/Rows/TM.lean#L184) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\varepsilon_0))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)(4,2)`](../lean/Rows/TM.lean#L188) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\psi_{\Omega}(Z(1))))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_0(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)`](../lean/Rows/TM.lean#L193) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\Omega_1))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(2,1)`](../lean/Rows/TM.lean#L197) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega+\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\Omega_1\cdot 2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,1)`](../lean/Rows/TM.lean#L201) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(0,\Omega+\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_1(\Omega_1)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,2)`](../lean/Rows/TM.lean#L206) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_1(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(2,2)`](../lean/Rows/TM.lean#L211) | $`\psi_{\Omega}(Z(1)+Z(1))`$ | $`\psi_0(\Omega_2\cdot 2)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 φ̄(ω²,0) を訂正 |
| [`(0,0)(1,1)(2,2)(2,2)(2,2)`](../lean/Rows/TM.lean#L214) | $`\psi_{\Omega}(Z(1)+Z(1)+Z(1))`$ | $`\psi_0(\Omega_2\cdot 3)`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)`](../lean/Rows/TM.lean#L218) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)))`$ | $`\psi_0(\psi_2(1))`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 φ̄(ω^ω,0) を訂正 |
| [`(0,0)(1,1)(2,2)(3,0)(3,0)`](../lean/Rows/TM.lean#L221) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+1))`$ | $`\psi_0(\psi_2(2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,0)`](../lean/Rows/TM.lean#L224) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\omega))`$ | $`\psi_0(\psi_2(\omega))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)`](../lean/Rows/TM.lean#L227) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\bar{\varphi}(1,0)))`$ | $`\psi_0(\psi_2(\varepsilon_0))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)`](../lean/Rows/TM.lean#L230) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\psi_{\Omega}(Z(1))))`$ | $`\psi_0(\psi_2(\psi_0(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |
| [`(0,0)(1,1)(2,2)(3,1)`](../lean/Rows/TM.lean#L234) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\Omega))`$ | $`\psi_0(\psi_2(\Omega_1))`$ |  | [oR](../lean/Trans/Recal.lean) |  |

## 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean)
