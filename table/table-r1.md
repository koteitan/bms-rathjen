# BMS × Rathjen T(M) 対応表 (R1)

<!-- このファイルは `lean/` の `lake exe gentable` による生成物。手編集しないこと。 -->

バージョン: v0.4.4

順序数表記と見做した BMS (活性化関数を任意化し `[n]` なしで扱う) と、
Rathjen の表記系 $`\mathfrak{T}(M)`$ (Rathjen, *Proof-theoretic analysis of KPM*,
Arch. Math. Logic 30 (1991), §2) の対応。

**証明列 ✅ の意味は下の [エビデンス](#エビデンス) を、設計の手順と失敗の記録は
[plan/](../plan/) を参照。**

## 対応表

| BMS | $`\mathfrak{T}(M)`$ | 通称 | 証明 | その他の弱いエビデンス | 備考 | [E 対象](#e-証明の対象行) |
|---|---|---|---|---|---|---|
| [`(空)`](../lean/Rows/TM.lean#L97) | $`0`$ | $`0`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 空行列 |  |
| [`(0)`](../lean/Rows/TM.lean#L99) | $`1`$ | $`1`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |  |
| [`(0)(0)`](../lean/Rows/TM.lean#L100) | $`2`$ | $`2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |  |
| [`(0)(1)`](../lean/Rows/TM.lean#L101) | $`\omega`$ | $`\omega`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  | **M** 1 行行列で成分が増える最初。**T** φ̄ の第 2 引数が 0 でなくなる最初 |
| [`(0)(1)(0)(1)`](../lean/Rows/TM.lean#L104) | $`\omega+\omega`$ | $`\omega\cdot 2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |  |
| [`(0)(1)(1)`](../lean/Rows/TM.lean#L106) | $`\bar{\varphi}(0,2)`$ | $`\omega^2`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |  |
| [`(0)(1)(2)`](../lean/Rows/TM.lean#L108) | $`\bar{\varphi}(0,\omega)`$ | $`\omega^\omega`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |  |
| [`(0)(1)(2)(3)`](../lean/Rows/TM.lean#L110) | $`\bar{\varphi}(0,\bar{\varphi}(0,\omega))`$ | $`\omega^{\omega^\omega}`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  |  |
| **<(0,0)(1,1)** | $`\lt\bar{\varphi}(1,0)`$ | $`\lt\varepsilon_0`$ |  | [checkAll](../lean/Test/TransTest.lean) | 区間の全標準行列 (stdSeq) の E3 を一般定理で一括証明 |  |
| [`(0,0)(1,1)`](../lean/Rows/TM.lean#L113) | $`\bar{\varphi}(1,0)`$ | $`\varepsilon_0`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) | 2 行の最初の極限 | **M** 2 行の最初。**T** φ̄ の第 1 引数が 0 でなくなる最初。**B** Ω₁ の最初 |
| [`(0,0)(1,1)(0,0)`](../lean/Rows/TM.lean#L116) | $`\bar{\varphi}(1,0)+1`$ | $`\varepsilon_0+1`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(1,0)`](../lean/Rows/TM.lean#L118) | $`\bar{\varphi}(0,\bar{\varphi}(1,0))`$ | $`\omega^{\varepsilon_0+1}`$ | [✅](../lean/Evidence/Cert.lean) | [o](../lean/Trans/TM.lean)+[bisim6](../lean/Evidence/Bisim.lean) |  | **T** φ̄ が不動点を飛ばす最初 (φ̄(0,ε₀) は ε₀ ではない) |
| [`(0,0)(1,1)(1,1)`](../lean/Rows/TM.lean#L121) | $`\bar{\varphi}(1,1)`$ | $`\varepsilon_1`$ |  | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(2,0)`](../lean/Rows/TM.lean#L123) | $`\bar{\varphi}(1,\omega)`$ | $`\varepsilon_\omega`$ |  | [o](../lean/Trans/TM.lean) |  | **M** 0 行目が 2 になる最初 |
| [`(0,0)(1,1)(2,0)(0,0)`](../lean/Rows/TM.lean#L126) | $`\bar{\varphi}(1,\omega)+1`$ | $`\varepsilon_\omega+1`$ |  | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(2,0)(1,1)(1,0)(2,1)(3,0)(1,0)(2,1)`](../lean/Rows/TM.lean#L129) | $`\bar{\varphi}(0,\bar{\varphi}(1,\omega+1)+\bar{\varphi}(1,\omega)+\bar{\varphi}(1,0))`$ | $`\bar{\varphi}(0,\bar{\varphi}(1,\omega+1)+\bar{\varphi}(1,\omega)+\bar{\varphi}(1,0))`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 1) | **D** 外部の表と食い違う 9 行の 1 つ |
| [`(0,0)(1,1)(2,0)(2,0)`](../lean/Rows/TM.lean#L135) | $`\bar{\varphi}(1,\bar{\varphi}(0,2))`$ | $`\varepsilon_{\omega^2}`$ |  | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(2,0)(3,0)`](../lean/Rows/TM.lean#L137) | $`\bar{\varphi}(1,\bar{\varphi}(0,\omega))`$ | $`\varepsilon_{\omega^\omega}`$ |  | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L140) | $`\bar{\varphi}(1,\bar{\varphi}(1,0))`$ | $`\varepsilon_{\varepsilon_0}`$ |  | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L142) | $`\bar{\varphi}(2,0)`$ | $`\zeta_0`$ |  | [o](../lean/Trans/TM.lean) |  | **M** (2,1) の最初。**B** ψ₁ が入れ子になる最初 |
| [`(0,0)(1,1)(2,1)(0,0)`](../lean/Rows/TM.lean#L145) | $`\bar{\varphi}(2,0)+1`$ | $`\zeta_0+1`$ |  | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(2,1)(1,0)`](../lean/Rows/TM.lean#L147) | $`\bar{\varphi}(0,\bar{\varphi}(2,0))`$ | $`\omega^{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(2,1)(1,1)`](../lean/Rows/TM.lean#L149) | $`\bar{\varphi}(1,\bar{\varphi}(2,0))`$ | $`\varepsilon_{\zeta_0+1}`$ |  | [o](../lean/Trans/TM.lean) |  |  |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(1,1)(2,0)`](../lean/Rows/TM.lean#L153) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\omega)`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\omega)`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 2) | **D** 外部の表と食い違う 9 行の 1 つ |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(1,1)(2,0)(3,1)`](../lean/Rows/TM.lean#L159) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\bar{\varphi}(1,0))`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(2,0))+\bar{\varphi}(1,0))`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 2) | **D** 外部の表と食い違う 9 行の 1 つ |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)`](../lean/Rows/TM.lean#L166) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)))))`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)))))`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 3) | **D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側 |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)(6,1)`](../lean/Rows/TM.lean#L172) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(1,0)))))`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(1,0)))))`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 3) | **D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側 |
| [`(0,0)(1,1)(2,1)(1,1)(2,0)(3,1)(4,1)(3,1)(4,0)(5,1)(6,1)(5,0)(6,1)(7,1)`](../lean/Rows/TM.lean#L178) | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(2,0)))))`$ | $`\bar{\varphi}(1,\bar{\varphi}(1,\bar{\varphi}(0,\bar{\varphi}(0,\bar{\varphi}(2,0)+\bar{\varphi}(2,0)))))`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 3) | **D** 外部の表と食い違う 9 行の 1 つ。当方が大きい側 |
| [`(0,0)(1,1)(2,1)(2,0)`](../lean/Rows/TM.lean#L190) | $`\bar{\varphi}(2,\omega)`$ | $`\zeta_\omega`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ε_{ζ₀·ω} を訂正 (較正事故) |  |
| [`(0,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L193) | $`\bar{\varphi}(3,0)`$ | $`\bar{\varphi}(3,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ₁ を訂正 (較正事故の初検出行) |  |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)`](../lean/Rows/TM.lean#L197) | $`\bar{\varphi}(1,\bar{\varphi}(3,\omega))`$ | $`\bar{\varphi}(1,\bar{\varphi}(3,\omega))`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 4) | **D** 外部の表と食い違う 9 行の 1 つ |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)`](../lean/Rows/TM.lean#L203) | $`\bar{\varphi}(2,\bar{\varphi}(3,\omega))`$ | $`\bar{\varphi}(2,\bar{\varphi}(3,\omega))`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 4) | **D** 外部の表と食い違う 9 行の 1 つ |
| [`(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)(2,1)`](../lean/Rows/TM.lean#L210) | $`\bar{\varphi}(3,\omega+1)`$ | $`\bar{\varphi}(3,\omega+1)`$ |  | [oR](../lean/Trans/Recal.lean) | 外部の表と食い違う ([diff.md](../diff.md) 族 4) | **D** 外部の表と食い違う 9 行の 1 つ |
| [`(0,0)(1,1)(2,1)(3,0)`](../lean/Rows/TM.lean#L216) | $`\bar{\varphi}(\omega,0)`$ | $`\bar{\varphi}(\omega,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ_ω を訂正 | **T** φ̄ の第 1 引数が数字でなくなる最初 |
| [`(0,0)(1,1)(2,1)(3,0)(4,1)`](../lean/Rows/TM.lean#L219) | $`\bar{\varphi}(\bar{\varphi}(1,0),0)`$ | $`\bar{\varphi}(\varepsilon_0,0)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 ζ_{ε₀} を訂正 | **T** φ̄ の第 1 引数が ε 数になる最初 |
| [`(0,0)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L222) | $`\psi_{\Omega}(0)`$ | $`\Gamma_0`$ |  | [oR](../lean/Trans/Recal.lean) | ψ 項の初登場。旧値 φ̄(3,0) を訂正 | **M** (3,1) の最初。**T** ψ の最初。**B** ψ₁ の 3 重入れ子の最初 |
| [`(0,0)(1,1)(2,1)(3,1)(0,0)`](../lean/Rows/TM.lean#L226) | $`\psi_{\Omega}(0)+1`$ | $`\Gamma_0+1`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,1)(3,1)(1,0)`](../lean/Rows/TM.lean#L228) | $`\bar{\varphi}(0,\psi_{\Omega}(0))`$ | $`\omega^{\Gamma_0+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)`](../lean/Rows/TM.lean#L240) | $`\psi_{\Omega}(Z(1))`$ | $`\psi_0(\Omega_2)`$ |  | [oR](../lean/Trans/Recal.lean) | 行 1 に 2 が現れる最初の行。旧値 φ̄(ω,0) を訂正 | **M** 1 行目に 2 が現れる最初。**T** Z の最初。**B** Ω₂ の最初 |
| [`(0,0)(1,1)(2,2)(1,1)`](../lean/Rows/TM.lean#L244) | $`\bar{\varphi}(1,\psi_{\Omega}(Z(1)))`$ | $`\varepsilon_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)`](../lean/Rows/TM.lean#L247) | $`\bar{\varphi}(2,\psi_{\Omega}(Z(1)))`$ | $`\zeta_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`](../lean/Rows/TM.lean#L250) | $`\psi_{\Omega}(Z(1)+1)`$ | $`\Gamma_{\psi_0(\Omega_2)+1}`$ |  | [oR](../lean/Trans/Recal.lean) |  | **T** ψ の引数に Z と和が同居する最初 |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L254) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2))`$ |  | [oR](../lean/Trans/Recal.lean) |  | **T** Ω が φ̄ の引数に現れる最初。**B** ψ₁ の引数に Ω₂ が入る最初 |
| [`(0,0)(1,1)(2,2)(1,1)(2,2)(1,1)(2,2)`](../lean/Rows/TM.lean#L258) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2)\cdot 2)`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,0)`](../lean/Rows/TM.lean#L262) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+1))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(2,0)`](../lean/Rows/TM.lean#L266) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+1))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,0)`](../lean/Rows/TM.lean#L270) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\omega))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)`](../lean/Rows/TM.lean#L274) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,0)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\varepsilon_0))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,0)(3,1)(4,2)`](../lean/Rows/TM.lean#L278) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\psi_{\Omega}(Z(1))))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_0(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,1)`](../lean/Rows/TM.lean#L283) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\Omega_1))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(2,1)`](../lean/Rows/TM.lean#L287) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\Omega+\Omega))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\Omega_1\cdot 2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,1)`](../lean/Rows/TM.lean#L291) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(0,\Omega+\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_1(\Omega_1)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,1)(3,2)`](../lean/Rows/TM.lean#L296) | $`\psi_{\Omega}(Z(1)+\bar{\varphi}(0,\bar{\varphi}(1,\Omega)+\bar{\varphi}(1,\Omega)))`$ | $`\psi_0(\Omega_2+\psi_1(\Omega_2+\psi_1(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(2,2)`](../lean/Rows/TM.lean#L301) | $`\psi_{\Omega}(Z(1)+Z(1))`$ | $`\psi_0(\Omega_2\cdot 2)`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 φ̄(ω²,0) を訂正 | **B** ψ₀ の引数が和になる最初 |
| [`(0,0)(1,1)(2,2)(2,2)(2,2)`](../lean/Rows/TM.lean#L305) | $`\psi_{\Omega}(Z(1)+Z(1)+Z(1))`$ | $`\psi_0(\Omega_2\cdot 3)`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(3,0)`](../lean/Rows/TM.lean#L309) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)))`$ | $`\psi_0(\psi_2(1))`$ |  | [oR](../lean/Trans/Recal.lean) | 旧値 φ̄(ω^ω,0) を訂正 | **M** (2,2) の後に (3,0) が来る最初。**T** Z が ω 冪の中に入る最初 |
| [`(0,0)(1,1)(2,2)(3,0)(3,0)`](../lean/Rows/TM.lean#L313) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+1))`$ | $`\psi_0(\psi_2(2))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,0)`](../lean/Rows/TM.lean#L316) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\omega))`$ | $`\psi_0(\psi_2(\omega))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)`](../lean/Rows/TM.lean#L319) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\bar{\varphi}(1,0)))`$ | $`\psi_0(\psi_2(\varepsilon_0))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)`](../lean/Rows/TM.lean#L322) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\psi_{\Omega}(Z(1))))`$ | $`\psi_0(\psi_2(\psi_0(\Omega_2)))`$ |  | [oR](../lean/Trans/Recal.lean) |  |  |
| [`(0,0)(1,1)(2,2)(3,1)`](../lean/Rows/TM.lean#L326) | $`\psi_{\Omega}(\bar{\varphi}(0,Z(1)+\Omega))`$ | $`\psi_0(\psi_2(\Omega_1))`$ |  | [oR](../lean/Trans/Recal.lean) |  | **B** ψ₂ の引数に Ω₁ が入る最初。表の最上行 |

# エビデンス

対応表の 1 行 $`(M, t)`$ について、**Lean の定理として存在するもの**だけを挙げる。
`E.` は行についての定理、`P.` はその補助命題、`D.` は定義。
Lean に無いもの — 順序型による主定理、順序埋め込みの一般形、各表記系の構造定理 —
は目標であってエビデンスではないので、ここには書かず
[plan/README.md](../plan/README.md) にある。

- [E 証明の対象行](#e-証明の対象行)
- [E.zero / E.succ / E.lim — ✅ の実体](#ezero--esucc--elim---の実体)
  - [✅ が検査していないもの](#-が検査していないもの)
- [E.cofinal (展開と基本列の相互共終)](#ecofinal-展開と基本列の相互共終)
- [証明書の強さと、その限界](#証明書の強さとその限界)
- [その他の弱いエビデンス](#その他の弱いエビデンス)
- [**Γ₀ より上の行について — 値を信用しないこと**](#γ₀-より上の行について--値を信用しないこと)
- [定義](#定義): [D.TM](#dtm-mathfraktm) · [D.CertifiedIn / D.DomI](#dcertifiedin--ddomi)

## E 証明の対象行

全 60 行の E を証明するのは大きすぎるので、**手で選んだ 23 行から始める**。網羅ではない。
選定の基準は「相が変わるところ」— これまで出てこなかった構成子が初めて現れる行、
違う変数を使い始める行 — と、外部の表と食い違う行である。表の一番右の列にその理由を
書いてある。印は相が属する側を表す。

| 印 | 側 | 何を見ているか |
|---|---|---|
| **M** | BMS | 行列の形。行数、成分が取る値、初めて現れる列の型 |
| **T** | $`\mathfrak{T}(M)`$ | 項の構成子。$`\bar\varphi`$ の引数の種類、$`\psi`$、$`Z`$、$`\Omega`$ |
| **B** | Buchholz $`\mathrm{OT}_B`$ | $`\psi_u`$ の添字 $`u`$、入れ子、引数が和になるところ |
| **D** | — | 外部の表と食い違う 9 行。値そのものが未決 ([diff.md](../diff.md)) |

**D の 9 行は他と性格が違う。** ほかの印は「ここが証明できれば周りも同じ理屈で通る」
という意味だが、D は「どちらが正しいか分かっていない」という意味である。9 行はすべて
Veblen 断片にあるので $`\psi`$・$`Z`$ の領域には入らない。決着に要るのは行ごとの
添字を固定した上での

```math
\mathrm{oR}\,(M[n]) = \mathrm{fsN}\,(\mathrm{oR}\,M)\,n
```

で、これは ✅ の行が満たしている E3 そのものである。

**選定は手作業で、網羅を主張しない。** 相の変わり目を機械で数え上げれば、ここに無い行も
出てくる。ここにあるのは「まずこれだけやれば、各側の主要な段差を一度は通る」という
出発点である。

## E.zero / E.succ / E.lim — ✅ の実体

**表の ✅ 列は $`\mathrm{Certified}\;M\;t`$ が存在する行にだけ機械的に付く。**
$`\mathrm{Certified}`$ は帰納的述語で、**行の $`\mathrm{kind}`$ によってどの規則が
適用されるかが決まる**。

### E.zero

空行列の行。前提は無く、無条件に成り立つ。

```math
\mathrm{Certified}\;[\,]\;0
```

### E.succ

```math
\begin{aligned}
&\mathrm{kind}\,M = \mathrm{succ} \;\Longrightarrow \cr
&\quad \Bigl[\; \mathrm{Certified}\;M\;u \;\Longleftrightarrow\;
   \exists t.\; u = t+1 \cr
&\qquad\qquad\quad \land\; \forall n.\;\mathrm{Certified}\;(M[n])\;t \;\Bigr]
\end{aligned}
```

すべての展開が同じ $`t`$ を認証するなら、この行は $`t+1`$。

### E.lim

```math
\begin{aligned}
&\mathrm{kind}\,M = \mathrm{lim} \;\Longrightarrow \cr
&\quad \Bigl[\; \mathrm{Certified}\;M\;t \;\Longleftrightarrow\;
   \exists f : \mathbb{N} \to \mathfrak{T}(M).\;
   \forall n.\;\mathrm{Certified}\;(M[n])\;(f_n) \cr
&\qquad\qquad\quad \land\; \forall n.\;f_n < t \cr
&\qquad\qquad\quad \land\; \forall n.\;f_n < f_{n+1} \cr
&\qquad\qquad\quad \land\; \forall s \in \mathfrak{T}(M).\;s < t \to \exists n.\;s \le f_n \;\Bigr]
\end{aligned}
```

**$`f`$ は $`\exists`$ で束縛された列である** — $`\mathbb{N}`$ の各点に
$`\mathfrak{T}(M)`$ の項を 1 つ与える写像であり、どこかに定義された特定の列ではない。
**表を読むときに $`f`$ の定義を探す必要はない。無いのが正しく、行ごとに証明が
自分で 1 つ選んで与える。**

**ただし選べるのは見かけだけである。** 4 つの連言のうち
**$`f_n`$ が何であるかを言うのは第 1 のものだけ**で、残る 3 つは
「$`t`$ 未満」「増加」「$`t`$ に共終」という $`f`$ の**性質**を述べるにすぎない。
そして性質は列を 1 つに絞らない。

実例を挙げる。$`\varepsilon_1`$ の行で基本列の候補を 3 つ立て、**3 つとも**
各添字で増加・$`\varepsilon_1`$ 未満・共終であることを実測で確認した。
それでも正しい列はその 3 つのどれでもなく、**第 4 のもの**

```math
\varepsilon_0,\quad \omega^{\varepsilon_0 \cdot 2},\quad
\omega^{\omega^{\varepsilon_0 \cdot 2}},\quad \dots
```

だった。**性質をいくつ確かめても列は決まらない**
([plan/constitutions.md](../plan/constitutions.md) C2)。

決めるのは第 1 の連言である。$`f_n`$ は $`M[n]`$ が認証した値**そのもの**でなければ
ならないので、$`f`$ を選んでいるのは**行列**であって $`\mathfrak{T}(M)`$ 側の都合ではない。
だから $`f`$ が $`\mathfrak{T}(M)`$ の標準基本列と一致する必要はどこにも無い。

### ✅ が検査していないもの

第 5 前提 $`\forall s \in \mathfrak{T}(M).\;s \lt t \to \exists n.\;s \le f_n`$ は
**$`f`$ が $`t`$ に共終**だと言っている。これと第 2・第 3 前提から
$`\sup_n f_n = t`$ が出る。**$`\mathfrak{T}(M)`$ 側の共終性は証明の中にある。**

言っていないのは BMS 側である:

```math
\sup_n |M[n]| = |M|
```

これが無いと $`\sup_n f_n = t`$ から $`|M| = t`$ へ渡れない。そして本リポジトリに
$`|M[n]| \lt |M|`$ も展開列の共終性も**補題として存在しない**。BMS を順序数表記として
読むとき極限行の値が展開の上限であることは**読み方の定義**であって、定理ではないからである。
✅ はこの読み方を仮定した上で $`\mathfrak{T}(M)`$ 側を尽くしている。

なお下の E.cofinal は**この穴を埋めるものではない**。あちらは
$`\mathfrak{T}(M)`$ の**標準基本列**と展開列の関係であり、$`f`$ は標準基本列である
必要がないので、E.cofinal を確かめても ✅ の根拠は増えない。両者は別の主張である
(詳細は [plan/README.md の E3 節](../plan/README.md#e3-展開と基本列の整合--本体のエビデンス))。

## E.cofinal (展開と基本列の相互共終)

$`\mathfrak{T}(M)`$ の**標準基本列**と BMS の展開列を突き合わせる形の証拠。
✅ の無い行のためのもので、**✅ の根拠ではない** — ✅ が要る共終性は
$`\mathrm{Certified}`$ の第 4 連言として既に、しかも $`o`$ に触れない形で入っている。

この形をなぜ等式ではなく相互共終で立てるのか、等式で立てると何を取り違えるのかは
**設計の話なので** [plan/README.md の E3 節](../plan/README.md#e3-展開と基本列の整合--本体のエビデンス)
にある。

## 証明書の強さと、その限界

E.certified がこの行について言えることの範囲を、定理として:

**一意性** — 導出に現れる値がすべて $`\mathfrak{T}(M)`$ の項である証明書の範囲では、
この行は $`t`$ 以外の値を取り得ない。上下いずれの側も排除されている。

```math
\forall u.\;\;\mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;u \;\Longrightarrow\; u = t
```

**上限 (無条件)** — 値が $`\mathfrak{T}(M)`$ の外に出るものも含め、いかなる証明書も
$`\omega^{t+1}`$ 以上を与えない。$`\mathrm{DomI}`$ の仮定が無いことに注意。

```math
\forall u.\;\;\mathrm{Certified}\;M\;u \;\Longrightarrow\; \bar\varphi(0,\,t+1) \not\le u
```

**ε₀ 行の鋭い上限** — この行では $`\varepsilon_0`$ の直上から塞がれている。

```math
\forall u.\;\; \varepsilon_0 < u \;\Longrightarrow\;
\neg\,\mathrm{Certified}\;[(0,0)(1,1)]\;u
```

**まだ排除できていないこと** — $`t`$ より**下**の値が、$`\mathfrak{T}(M)`$ の外へ出る
部分値を経由して認証される可能性:

```math
\exists u.\;\; u < t \;\wedge\; \mathrm{Certified}\;M\;u
\;\wedge\; \neg\,\mathrm{CertifiedIn}\;\mathrm{DomI}\;M\;u \;\;?
```

上側は無条件に塞がっているので**残る穴は片側のみ**。P.undershoot_reduction により
葉 1 枚に還元済み:

> **P.T** $`a \le b \to b \le c \to a \le c`$ — 中間項 $`b`$ が
> $`\mathrm{Frag2}`$、**両端点は任意**

## その他の弱いエビデンス

いずれも有限個の計算検査であり、較正誤りを検出できない。順序埋め込みも corpus 上の
`Evidence.Check.checkE2` という計算検査としてのみ存在し、定理ではないのでここに置く。

| 記号 | 意味 |
|---|---|
| `o` | 翻訳関数がこの行列で定義され $`o(M) = t`$ (両辺を同じ写像で計算するので較正誤りは検出できない) |
| `oR` | オラクル較正済みの候補値。**2 段の合成**で、定義域は BMS の 2 行断片 (下記)。全行一致をビルド時 `#guard` で強制 |
| `bisim6` | 深さ 6 の双模倣 |
| `oStageC` | Stage C の候補翻訳の値の一致 |

### `oR` が何の合成なのか

`oR` は変換写像そのものではなく、**2 段の合成**である。

```math
\mathrm{BMS}\ \xrightarrow{\ \text{oracle}\ }\ \mathrm{OT}_B
\ \xrightarrow{\ \mathrm{dict}\ }\ \mathfrak{T}(M)
```

1 段目が P進大好きbot 氏の変換写像 (PSS 停止性証明のもの、naruyoko 氏の実装) で、
その行き先は **Buchholz の表記系 $`\mathrm{OT}_B`$** — $`D_u a = \psi_u(a)`$
(Buchholz 1986) であって、Rathjen の $`\mathfrak{T}(M)`$ ではない。
2 段目 `dict` がこのリポジトリの用意する辞書である。像への順序同型で値を保つ**という
主張**だが、**それは定理ではなく測定**である。

**$`D_u`$ は Rathjen の $`\psi_{\Omega_{u+1}}`$ ではない。** 土台が違う:

| | Veblen 関数 | $`\psi`$ の始まり |
|---|---|---|
| Buchholz $`\mathrm{OT}_B`$ | 持たない。Veblen 階層は $`D_0`$ の引数の中の $`\Omega`$ 冪として符号化される | — |
| Rathjen $`\mathfrak{T}(M)`$ | 2 変数 $`\bar\varphi`$ が $`(0,M)`$ 全体で原始的 | Veblen が止まる所から。$`\psi_{Z0}(0) = \Gamma_0`$ |

だから `dict` は名前の付け替えではなく、**本物の翻訳**である。

**定義域は BMS の 2 行断片**である — 各列の高さが 2 以下で、行列が空でないもの。
その外では `oR` は `none` を返す。表の行はすべてこの範囲に収まる。
**表がこの断片の外へ伸びることは、いまの `oR` ではできない。**

## Γ₀ より上の行について — 値を信用しないこと

**この節の内容は 2026-08-12 に判明したもので、当該行の値はまだ直っていない。**

`(0,0)(1,1)(2,2)` 以上の行の値は `oR = (1+\cdot) \circ \mathrm{dict} \circ \mathrm{oRB}`
から来ている。この `dict` について、次が証明されている (`lean/Trans/Dict.lean` §4)。

**外部資料と食い違う。** BMS `(0,0)(1,1)(2,2)` の Buchholz 値 $`\psi_0(\psi_2(0))`$ には
3 者が一致している (このリポジトリの pss2bp 移植、Hexirp 氏の解析、スプレッドシート)。
食い違うのはそこから $`\mathfrak{T}(M)`$ へ翻訳する段だけである。

```math
\mathrm{dict} \;\longmapsto\; \psi_\Omega(Z(1)) \qquad
\text{資料} \;\longmapsto\; \psi_\Omega(\bar\varphi(1, \Omega+1))
```

両方とも正規形で、等しくなく、資料の値のほうが真に小さい (3 本とも `decide` で証明済み)。
資料側には $`\mathfrak{T}(M)`$ を直接与える 3 つ目の独立な資料が加わり
(Hexirp 氏の BMS↔Rathjen 対応表、`scripts/hexirp-rathjen-check.py` で再実行できる)、
そこでも同じ $`\psi_\Omega(\bar\varphi(1, \Omega+1))`$ である。
資料はいずれも未証明なので**どちらが正しいかはここでは決まらない**が、
`dict` 側に立つ資料は 1 つも無い。

**ここには「`dict` は順序を保存しないので翻訳として失格」と書いてあったが、取り消した
(2026-08-12)。** 反例の母集団を外部の標準形判定器で作っており、その判定器に
コールバックの引数取り違えのバグがあった。正しい判定器で作り直した母集団
(標準形 3193 個、順序対 5096028 組) では**順序反転は 0 件**である。詳細と、
誤って通っていた 3 項を固定した陰性対照は `Trans/Dict.lean` §4 にある。

**根はもっと深い。** [`lean/TM/Terms.lean`](../lean/TM/Terms.lean) はこのリポジトリの
$`\chi`$ を `Z a = χ_a(0)` と 1 引数に潰している。しかし原典では $`\chi`$ は 2 引数で、
**第 2 引数が $`\Omega`$ 階層を枚挙する**:

```math
\chi_0(\alpha) = \Omega_{1+\alpha}, \qquad
\chi_1(0) = I \;(\text{最小の弱到達不能基数})
```

つまり `Z 1` は $`\Omega_2`$ ではなく $`I`$ であり、
**$`\Omega_2 = \chi_0(1)`$ は現在の型では書けない**。
当該の行はその $`\Omega_2`$ が要る領域にある。値を直すには型を変える必要があり、
それは $`\mathfrak{T}(M)`$ の項型とその上のすべてに波及するので、まだ着手していない。

**したがって、これらの行の値は資料と食い違ったままであり、信用してはいけない。**
✅ の付いた行は影響を受けない —
✅ は `Certified` から来ており、読み手を一度も通らないからである。

外部資料との突き合わせは [`scripts/external-check.py`](../scripts/external-check.py) で再実行できる。

# 定義

## D.TM ($`\mathfrak{T}(M)`$)

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

ここで $`AP`$ は加法的主要な項、$`SC`$ は強クリティカルな項、$`R`$ は正則:

```math
AP = \{M\} \cup \{\bar\omega^\alpha\} \cup \{\bar\varphi(\alpha,\beta)\} \cup SC,
\qquad
SC = \{M\} \cup \{\psi_\kappa\alpha\} \cup \{Z\alpha\},
\qquad
R = \{Z\alpha\}
```

$`\oplus`$ の条件 (成分が $`AP`$、降順) が一意な正規形を与える。

**$`\bar\varphi`$ は $`\omega^\cdot`$ の不動点を飛ばして数える。**
$`\bar\varphi(0,\beta)`$ は最初の不動点未満では $`\omega^\beta`$ だが、

```math
\bar\varphi(0, \varepsilon_0) = \omega^{\varepsilon_0 + 1} \ne \varepsilon_0
```

**不動点の下では 2 つの読みが一致するので、そこだけで較正した関数・コーパス・読者は
上で静かに誤る。**

## D.CertifiedIn / D.DomI

```math
\mathrm{DomI}(t) \;:\equiv\; t \in \mathfrak{T}(M)
```

$`\mathrm{Certified}`$ は認証される値に制約を課さないので、生の項の上では
$`\mathfrak{T}(M)`$ の項でない値も認証されうる (P.cert_not_single_valued):

```math
\mathrm{Certified}\;[(0)(1)]\;\omega
\qquad\text{かつ}\qquad
\mathrm{Certified}\;[(0)(1)]\;(1+M)
```

$`\mathrm{CertifiedIn}\;\mathrm{Dom}`$ は**導出に現れる値すべて**が
$`\mathrm{Dom}`$ に属することを要求する版。E.certified の一意性が
$`\mathrm{DomI}`$ を要求するのは、この一価性の破れを塞ぐためである。

# 実装

[行 DB と行ごとの検査](../lean/Rows/TM.lean) ·
[BMS の展開](../lean/BMS/Expand.lean) ·
[T(M) の項](../lean/TM/Terms.lean) ·
[T(M) の順序](../lean/TM/Order.lean) ·
[基本列](../lean/TM/FS.lean) ·
[証明書](../lean/Evidence/Cert.lean)
