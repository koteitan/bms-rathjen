# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.8.20

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`\mathfrak{T}(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応。

**証明列の ✅ は[証明の仕様](#証明の仕様)の E.cert が Lean の定理であることを意味する。**
それ以外の印は ✅ の材料であって ✅ ではない。**印はすべてビルドが計算して付ける**
(手で書けない)。

## 対応表

| BMS | $`\mathfrak{T}(M)`$ | Buchholz | 通称 | 証明 | その他の弱いエビデンス | 備考 |
|---|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L114) | $`0`$ | $`0`$ | $`0`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L44)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |
| [`(0)`](../lean/Rows/TM.lean#L116) | $`1`$ | $`\psi_{0}(0)`$ | $`1`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L57)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L117) | $`2`$ | $`\psi_{0}(0)+\psi_{0}(0)`$ | $`2`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L70)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L118) | $`\omega`$ | $`\psi_{0}(\psi_{0}(0))`$ | $`\omega`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L83)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L121) | $`\omega+\omega`$ | $`\psi_{0}(\psi_{0}(0))+\psi_{0}(\psi_{0}(0))`$ | $`\omega\cdot 2`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L96)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L123) | $`\bar{\varphi}(0,2)`$ | $`\psi_{0}(\psi_{0}(0)+\psi_{0}(0))`$ | $`\omega^2`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L109)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L125) | $`\bar{\varphi}(0,\omega)`$ | $`\psi_{0}(\psi_{0}(\psi_{0}(0)))`$ | $`\omega^\omega`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L122)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L127) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\psi_{0}(\psi_{0}(\psi_{0}(\psi_{0}(0))))`$ | $`\omega^{\omega^\omega}`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L135)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\psi_{0}(\psi_{1}(0))`$ | $`\lt\varepsilon_0`$ |  | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) について、展開の値を一般定理で一括証明 |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L130) | $`\bar{\varphi}(1,0)`$ | $`\psi_{0}(\psi_{1}(0))`$ | $`\varepsilon_0`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L343)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 |
| [`(0,0)(1,1)(0,0)`](../lean/Rows/TM.lean#L133) | $`\bar{\varphi}(1,0)+1`$ | $`\psi_{0}(\psi_{1}(0))+\psi_{0}(0)`$ | $`\varepsilon_0+1`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L152)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L135) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\psi_{0}(\psi_{1}(0)+\psi_{0}(0))`$ | $`\omega^{\varepsilon_0+1}`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L189)+[o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L138) | $`\bar{\varphi}(1,1)`$ | $`\psi_{0}(\psi_{1}(0)+\psi_{1}(0))`$ | $`\varepsilon_1`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L345)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L140) | $`\bar{\varphi}(1,\omega)`$ | $`\psi_{0}(\psi_{1}(\psi_{0}(0)))`$ | $`\varepsilon_\omega`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L346)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(0,0)`](../lean/Rows/TM.lean#L143) | $`\bar{\varphi}(1,\omega)+1`$ | $`\psi_{0}(\psi_{1}(\psi_{0}(0)))+\psi_{0}(0)`$ | $`\varepsilon_\omega+1`$ | [✅](../lean/Evidence/Cert.lean) | [fₙ](../lean/Rows/Proofs.lean#L269)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(1,1)(1,0)(2,1)(3,0)(1,0)(2,1)`](../lean/Rows/TM.lean#L146) | $`\bar{\varphi}(0,\bar{\varphi}(1,\omega+1)+\bar{\varphi}(1,\omega)+\bar{\varphi}(1,0))`$ | $`\psi_{0}(\psi_{1}(\psi_{0}(0))+\psi_{1}(0)+\psi_{0}(\psi_{1}(\psi_{0}(0)))+\psi_{0}(\psi_{1}(0)))`$ | $`\omega^{\varepsilon_{\omega+1}+\varepsilon_\omega+\varepsilon_0}`$ |  | [fₙ](../lean/Rows/Selected.lean#L312) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 1) |
| [`(0,0)(1,1)(2,0)(2,0)`](../lean/Rows/TM.lean#L152) | $`\bar{\varphi}(1,\bar{\varphi}(0,2))`$ | $`\psi_{0}(\psi_{1}(\psi_{0}(0)+\psi_{0}(0)))`$ | $`\varepsilon_{\omega^2}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L299)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,0)`](../lean/Rows/TM.lean#L154) | $`\bar{\varphi}(1,\bar{\varphi}(0,\omega))`$ | $`\psi_{0}(\psi_{1}(\psi_{0}(\psi_{0}(0))))`$ | $`\varepsilon_{\omega^\omega}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L284)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L157) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\psi_{0}(\psi_{1}(\psi_{0}(\psi_{1}(0))))`$ | $`\varepsilon_{\varepsilon_0}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L252)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L159) | $`\bar{\varphi}(2,0)`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0)))`$ | $`\zeta_0`$ |  | [fₙ](../lean/Rows/Proofs.lean#L348)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(0,0)`](../lean/Rows/TM.lean#L162) | $`\bar{\varphi}(2,0)+1`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0)))+\psi_{0}(0)`$ | $`\zeta_0+1`$ |  | [fₙ](../lean/Rows/Proofs.lean#L164)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,0)`](../lean/Rows/TM.lean#L164) | $`\bar{\varphi}(0,\bar{\varphi}(2,0))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{0}(0))`$ | $`\omega^{\zeta_0+1}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L191)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,1)`](../lean/Rows/TM.lean#L166) | $`\bar{\varphi}(1,\bar{\varphi}(2,0))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(0))`$ | $`\varepsilon_{\zeta_0+1}`$ |  | [fₙ](../lean/Rows/Proofs.lean#L234)+[o](../lean/Trans/TM.lean) |  |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(1,1)(2,0)`](../lean/Rows/TM.lean#L170) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\omega)`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(0)))+\psi_{1}(\psi_{0}(0)))`$ | $`\varepsilon_{\varepsilon_{\zeta_0+1}+\omega}`$ |  | [fₙ](../lean/Rows/Selected.lean#L573) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 2) |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L176) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\bar{\varphi}(1,0))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(0)))+\psi_{1}(\psi_{0}(\psi_{1}(0))))`$ | $`\varepsilon_{\varepsilon_{\zeta_0+1}+\varepsilon_0}`$ |  | [fₙ](../lean/Rows/Selected.lean#L843) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 2) |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)`](../lean/Rows/TM.lean#L183) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)))))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{0}(0))))))`$ | $`\varepsilon_{\varepsilon_{\omega^{\omega^{\zeta_0+1}}}}`$ |  | [fₙ](../lean/Rows/Selected.lean#L1046) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3) |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)(6,1)`](../lean/Rows/TM.lean#L189) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(1,0)))))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{0}(\psi_{1}(0)))))))`$ | $`\varepsilon_{\varepsilon_{\omega^{\omega^{\zeta_0+\varepsilon_0}}}}`$ |  | [fₙ](../lean/Rows/Selected.lean#L1348) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3) |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)(6,1)(7,1)`](../lean/Rows/TM.lean#L195) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(2,0)))))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{1}(\psi_{0}(\psi_{1}(\psi_{1}(0))+\psi_{0}(\psi_{1}(\psi_{1}(0))))))))`$ | $`\varepsilon_{\varepsilon_{\omega^{\omega^{\zeta_0\cdot 2}}}}`$ |  | [fₙ](../lean/Rows/Selected.lean#L1685) | 外部の表と食い違うが決着済み。当方が正しい ([diff.md](diff.md) 族 3) |
| [`(0,0)(1,1)(2,1)(2,0)`](../lean/Rows/TM.lean#L207) | $`\bar{\varphi}(2,\omega)`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0)+\psi_{0}(0)))`$ | $`\zeta_\omega`$ |  |  | 旧値 ε_{ζ₀·ω} を訂正 (較正事故) |
| [`(0,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L210) | $`\bar{\varphi}(3,0)`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0)+\psi_{1}(0)))`$ | $`\bar{\varphi}(3,0)`$ |  |  | 旧値 ζ₁ を訂正 (較正事故の初検出行) |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)`](../lean/Rows/TM.lean#L214) | $`\bar{\varphi}(1,\bar{\varphi}(3,\omega))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0)+\psi_{1}(0)+\psi_{0}(0))+\psi_{1}(0))`$ | $`\varepsilon_{\bar{\varphi}(3,\omega)+1}`$ |  | [fₙ](../lean/Rows/G9.lean#L6) | 外部の表と食い違う ([diff.md](diff.md) 族 4) |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L220) | $`\bar{\varphi}(2,\bar{\varphi}(3,\omega))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0)+\psi_{1}(0)+\psi_{0}(0))+\psi_{1}(\psi_{1}(0)))`$ | $`\zeta_{\bar{\varphi}(3,\omega)+1}`$ |  | [fₙ](../lean/Rows/G10.lean#L6) | 外部の表と食い違う ([diff.md](diff.md) 族 4) |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L227) | $`\bar{\varphi}(3,\omega+1)`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(0)+\psi_{1}(0)+\psi_{0}(0))+\psi_{1}(\psi_{1}(0)+\psi_{1}(0)))`$ | $`\bar{\varphi}(3,\omega+1)`$ |  | [fₙ](../lean/Rows/G11.lean#L36) | 外部の表と食い違う ([diff.md](diff.md) 族 4) |
| [`(0,0)(1,1)(2,1)(3,0)`](../lean/Rows/TM.lean#L233) | $`\bar{\varphi}(\omega,0)`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(\psi_{0}(0))))`$ | $`\bar{\varphi}(\omega,0)`$ |  | [fₙ](../lean/Rows/Selected.lean#L2114) | 旧値 ζ_ω を訂正 |
| [`(0,0)(1,1)(2,1)(3,0)(4,1)`](../lean/Rows/TM.lean#L237) | $`\bar{\varphi}(\bar{\varphi}(1,0),0)`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(\psi_{0}(\psi_{1}(0)))))`$ | $`\bar{\varphi}(\varepsilon_0,0)`$ |  | [fₙ](../lean/Rows/G3.lean#L6) | 旧値 ζ_{ε₀} を訂正 |
| [`(0,0)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L241) | $`\psi_{\Omega}(0)`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(\psi_{1}(0))))`$ | $`\Gamma_0`$ |  | [fₙ](../lean/Rows/G7.lean#L6) | ψ 項の初登場。旧値 φ̄(3,0) を訂正 |
| [`(0,0)(1,1)(2,1)(3,1)(0,0)`](../lean/Rows/TM.lean#L245) | $`\psi_{\Omega}(0)+1`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(\psi_{1}(0))))+\psi_{0}(0)`$ | $`\Gamma_0+1`$ |  |  |  |
| [`(0,0)(1,1)(2,1)(3,1)(1,0)`](../lean/Rows/TM.lean#L247) | $`\bar{\varphi}(0,\psi_{\Omega}(0))`$ | $`\psi_{0}(\psi_{1}(\psi_{1}(\psi_{1}(0)))+\psi_{0}(0))`$ | $`\omega^{\Gamma_0+1}`$ |  |  |  |
| [`(0,0)(1,1)(2,2)`](../lean/Rows/TM.lean#L259) | $`\psi_{\Omega}(Z(1))`$ | $`\psi_{0}(\psi_{2}(0))`$ | $`\psi_0(\Omega_2)`$ |  | [fₙ](../lean/Rows/G4.lean#L6) | 行 1 に 2 が現れる最初の行。旧値 φ̄(ω,0) を訂正 |
| [`(0,0)(1,1)(2,2)(1,1)`](../lean/Rows/TM.lean#L263) | $`\bar{\varphi}(1,\psi_{\Omega}(Z(1)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(0))`$ | $`\varepsilon_{\psi_0(\Omega_2)+1}`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)`](../lean/Rows/TM.lean#L266) | $`\bar{\varphi}(2,\psi_{\Omega}(Z(1)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{1}(0)))`$ | $`\zeta_{\psi_0(\Omega_2)+1}`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L269) | $`\psi_{\Omega}(Z(1)+1)`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{1}(\psi_{1}(0))))`$ | $`\Gamma_{\psi_0(\Omega_2)+1}`$ |  | [fₙ](../lean/Rows/G12.lean#L50) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L273) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2))`$ |  | [fₙ](../lean/Rows/G5.lean#L7) |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L277) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0))+\psi_{1}(\psi_{2}(0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2)\cdot 2)`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)`](../lean/Rows/TM.lean#L281) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+1))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(2,0)`](../lean/Rows/TM.lean#L285) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+1))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(0)+\psi_{0}(0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+2))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,0)`](../lean/Rows/TM.lean#L289) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(\psi_{0}(0))))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\omega))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)`](../lean/Rows/TM.lean#L293) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,0)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(\psi_{1}(0))))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\varepsilon_0))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)(4,2)`](../lean/Rows/TM.lean#L297) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\psi_{\Omega}(Z(1))))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{0}(\psi_{2}(0))))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_0(\Omega_2)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,1)`](../lean/Rows/TM.lean#L302) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{1}(0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\Omega_1))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(2,1)`](../lean/Rows/TM.lean#L306) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega+\Omega))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{1}(0)+\psi_{1}(0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\Omega_1\cdot 2))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,1)`](../lean/Rows/TM.lean#L310) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(0,\Omega+\Omega)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{1}(\psi_{1}(0))))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_1(\Omega_1)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,2)`](../lean/Rows/TM.lean#L315) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega)))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0)+\psi_{1}(\psi_{2}(0))))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_1(\Omega_2)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(2,2)`](../lean/Rows/TM.lean#L320) | $`\psi_{\Omega}(Z(1)+Z(1))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{2}(0))`$ | $`\psi_0(\Omega_2\cdot 2)`$ |  | [fₙ](../lean/Rows/G6.lean#L6) | 旧値 φ̄(ω²,0) を訂正 |
| [`(0,0)(1,1)(2,2)(2,2)(2,2)`](../lean/Rows/TM.lean#L325) | $`\psi_{\Omega}(Z(1)+Z(1)+Z(1))`$ | $`\psi_{0}(\psi_{2}(0)+\psi_{2}(0)+\psi_{2}(0))`$ | $`\psi_0(\Omega_2\cdot 3)`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,0)`](../lean/Rows/TM.lean#L329) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(0)))`$ | $`\psi_0(\psi_2(1))`$ |  | [fₙ](../lean/Rows/Selected.lean#L3557) | 旧値 φ̄(ω^ω,0) を訂正 |
| [`(0,0)(1,1)(2,2)(3,0)(3,0)`](../lean/Rows/TM.lean#L334) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+1))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(0)+\psi_{0}(0)))`$ | $`\psi_0(\psi_2(2))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,0)`](../lean/Rows/TM.lean#L337) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\omega))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(\psi_{0}(0))))`$ | $`\psi_0(\psi_2(\omega))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)`](../lean/Rows/TM.lean#L340) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\bar{\varphi}(1,0)))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(\psi_{1}(0))))`$ | $`\psi_0(\psi_2(\varepsilon_0))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)`](../lean/Rows/TM.lean#L343) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\psi_{\Omega}(Z(1))))`$ | $`\psi_{0}(\psi_{2}(\psi_{0}(\psi_{2}(0))))`$ | $`\psi_0(\psi_2(\psi_0(\Omega_2)))`$ |  |  |  |
| [`(0,0)(1,1)(2,2)(3,1)`](../lean/Rows/TM.lean#L347) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\Omega))`$ | $`\psi_{0}(\psi_{2}(\psi_{1}(0)))`$ | $`\psi_0(\psi_2(\Omega_1))`$ |  | [fₙ](../lean/Rows/G8.lean#L6) |  |

## 列の意味

| 列 | 中身 |
|---|---|
| BMS | 行列。リンク先は行の定義 |
| $`\mathfrak{T}(M)`$ | Rathjen R1 の項 ([D.TM](#dtm)) |
| Buchholz | Buchholz の $`\mathrm{OT}_B`$ での値。**全行が変換写像 (pss2bp) の出力**を $`\psi`$ 形で書いたもの ($`oR`$ の $`1+\cdot`$ 補正込み) |
| 通称 | 同じ順序数の通り名。$`\varepsilon_\alpha`$・$`\zeta_\alpha`$・$`\Gamma_\alpha`$・$`\omega^\alpha`$ を使う。通り名の無いところは $`\bar{\varphi}`$ のまま |
| 証明 | ✅ = [E.cert](#ecert) が定理。空欄 = まだ |
| その他の弱いエビデンス | ✅ の材料。[一覧](#その他の弱いエビデンス) |
| 備考 | その行に固有のこと |

# 証明の仕様

対応表の 1 行 $`(S, t)`$ の証明列に ✅ が付く条件は、これただ 1 つである。

## E.cert

```math
\mathrm{Certified}(S, t)
```

## D.Certified

**証明書** $`\mathrm{Certified} \subseteq \mathcal{S} \times \mathfrak{T}(M)`$ を、
次の 3 規則の**閉包** ([D.Cl](misc.md#dcl)) と定義する。

### D.Certified.zero

```math
\mathrm{Certified}([\;], 0)
```

### D.Certified.succ

```math
\begin{array}{rl}
 & \mathrm{kind}(S) = \text{後続} \cr
\land & \forall n \in \mathbb{N}.\; \mathrm{Certified}(S[n], t) \cr
\land & t+1 \in \mathfrak{T}(M) \cr
\longrightarrow & \mathrm{Certified}(S, t+1)
\end{array}
```

### D.Certified.lim

```math
\forall f : \mathbb{N} \to \mathfrak{T}(M).\;
\left(
\begin{array}{rl}
 & \mathrm{kind}(S) = \text{極限} \cr
\land & t \in \mathfrak{T}(M) \cr
\land & \forall n.\; \mathrm{Certified}(S[n], f_n) \cr
\land & \forall n.\; f_n \lt t \cr
\land & \forall n.\; f_n \lt f_{n+1} \cr
\land & \forall s \in \mathfrak{T}(M).\; s \lt t \;\to\; \exists n.\; s \le f_n \cr
\longrightarrow & \mathrm{Certified}(S, t)
\end{array}
\right)
```

$`\lt`$ は $`\mathfrak{T}(M)`$ の線形順序 ([Rathjen, 1991] 2.3)。

[T.Cl.inv](misc.md#tclinv) より逆も言える — $`\mathrm{Certified}(S, t)`$ が成り立つのは、
上の 6 条件を満たす $`f`$ が**存在するとき、かつそのときに限る**。

## D.TM

**Rathjen 表記の標準形** $`\mathfrak{T}(M)`$ を、次の規則の**閉包** ([D.Cl](misc.md#dcl)) と
定義する ([Rathjen, 1991] 2.1)。

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
\quad \alpha < M \quad K_\kappa(\alpha) < \alpha}
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
SC = \{M\} \cup \{\psi_\kappa(\alpha)\} \cup \{Z(\alpha)\},
\qquad
R = \{Z(\alpha)\}
```


## D.Matrix

**バシク行列**の全体 $`\mathcal{S}`$ を、**列** (自然数の有限列) の有限列全体と定義する。

```math
\mathcal{S} \;=\; \bigl(\mathbb{N}^{\ast}\bigr)^{\ast}
```

$`X^{\ast}`$ は $`X`$ の有限列全体を表す。列の本数も列の高さも固定しない。
高さを揃える必要も無い。対応表の行はすべて高さ 2 以下の列からなる。

記号は[数式的定義](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E6%95%B0%E5%BC%8F%E7%9A%84%E5%AE%9A%E7%BE%A9)
に合わせる — 行列を $`S`$、その $`x`$ 番目の列を $`S_x`$、その $`y`$ 成分を $`S_{xy}`$ と書く。
$`M`$ は最小の弱 Mahlo 基数だけを指し、行列には使わない。

## D.expand

**展開** $`S[n]`$ と**行の種別** $`\mathrm{kind}(S)`$ を、次の型の写像と定義する。

```math
\cdot[\cdot] \;:\; \mathcal{S} \times \mathbb{N} \to \mathcal{S}
\qquad\qquad
\mathrm{kind} \;:\; \mathcal{S} \to
\{\text{空}, \text{後続}, \text{極限}\}
```

規則は BM4 の展開規則そのもので、
[koteitan「バシク行列の数式的定義」](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E6%95%B0%E5%BC%8F%E7%9A%84%E5%AE%9A%E7%BE%A9)
に従う。実装は [BMS/Expand.lean](../lean/BMS/Expand.lean)。

# その他の弱いエビデンス

いずれも ✅ の材料であって ✅ ではない。$`f_n`$ 以外は有限個の計算検査であり、
較正誤りを検出できない。

| 記号 | 意味 | 全ての $`n`$? |
|---|---|---|
| $`f_n`$ | [E.fs](misc.md#efs) が Lean の定理 | はい |
| `o` | 翻訳関数がこの行列で定義され $`o(S) = t`$ (両辺を同じ写像で計算するので較正誤りは検出できない) | いいえ |
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

**根は型にある** ([D.TM](#dtm))。$`Z(1)`$ は $`\Omega_2`$ ではなく $`I`$ で、
$`\Omega_2 = \chi_0(1)`$ は現在の型では書けない。直すには項型を変える必要がある。

**✅ の付いた行は影響を受けない。** ✅ は [E.cert](#ecert) から来ており、
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

# 関連文書

- 作り方・作業手順・資料の場所 — [plan/README.md](../plan/README.md)
- 表を読むとき・書くときの原則 (注意書き) — [plan/constitutions.md](../plan/constitutions.md)
- この表自身の仕様 — [plan/spec.md](../plan/spec.md)
- 外部の対応表との差分 — [diff.md](diff.md)
- 本筋から外した補足 — [misc.md](misc.md)
