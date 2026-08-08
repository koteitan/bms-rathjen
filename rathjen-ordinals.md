# Rathjen の順序数表記系一覧(強さ順)

BMS との対応表を作るにあたり、ターゲットとなる Rathjen の順序数崩壊関数
(ordinal collapsing function, OCF)を強さ順に整理する。
各行の「証明論的順序数」はその表記系が測る理論の証明論的順序数
(= その表記系の可算部分の極限)である。

出典は各行の書誌情報を参照。

## 前提となる文脈(Rathjen 以前)

| 表記系 | 使用する大基数 | 解析対象理論 | 極限の順序数 | 出典 |
|---|---|---|---|---|
| Buchholz $`\psi_\nu`$ | $`\Omega_\nu`$ ($`\nu\le\omega`$) | $`\Pi^1_1\text{-CA}+\mathrm{BI}`$ | $`\psi_0(\varepsilon_{\Omega_\omega+1})`$ (Takeuti–Feferman–Buchholz) | Buchholz 1986 |
| Jäger $`T(J)`$ | $`I`$ (最小弱到達不能基数) | $`\mathrm{KPi}`$ ($`=\Delta^1_2\text{-CA}+\mathrm{BI}`$) | $`\psi_{\Omega_1}(\varepsilon_{I+1})`$ | Jäger 1984 |

- 2 行 BMS (= PSS) の極限は $`\psi_0(\Omega_\omega)`$ (Buchholz)。p進大好きbot による証明があり、
  [pss-proof](https://github.com/koteitan/pss-proof) に LEAN 形式化がある。
- [BM4-Analysis](https://docs.google.com/spreadsheets/d/1Y4BV65KNPjJ6uBtBBFYDXKo6PFlmEuowyn39XmLh4MI/edit?usp=sharing)
  の最初のシート "To psi(I)" は Jäger レベル、
  それ以降のシートは下記 Rathjen の各系に対応する。

## Rathjen の表記系(強さ順)

| # | 表記系 | 使用する大基数 | 主要関数 | 解析対象理論 | 証明論的順序数 | 出典(年) |
|---|---|---|---|---|---|---|
| R1 | $`T(M)`$ | $`M`$ = 最小弱 Mahlo 基数 | $`\chi_\alpha\colon \varepsilon_{M+1}\to M`$ (Mahlo 崩壊), $`\psi_\kappa`$ | $`\mathrm{KPM}`$ | $`\psi_{\Omega_1}(\varepsilon_{M+1})`$ | 1990 (定義), 1991 (KPM 解析) |
| R1' | $`T(M)`$ の再帰版 | $`\mu`$ = 最小 recursively Mahlo(大基数を使わない再構成) | 同上 | $`\mathrm{KPM}`$ (整列証明・下界) | 同上 | 1994 (well-ordering proof) |
| R2 | $`T(K)`$ | $`K`$ = 最小弱コンパクト基数 ($`\Pi^1_1`$-indescribable) | $`\Xi`$, $`\Psi^\xi_\pi`$ | $`\mathrm{KP}+\Pi_3\text{-Ref}`$ | $`\Psi^0_{\Omega_1}(\varepsilon_{K+1})`$ (Cor. 10.5, sharp) | 1994 (Proof theory of reflection) |
| R2' | $`T(K)`$ の一般化 | $`\Pi^1_{n-2}`$-indescribable 基数 | 同上の $`n`$ 版 | $`\mathrm{KP}+\Pi_n\text{-Ref}`$ | (論文は $`\Pi_3`$ に集中、手法は一般の $`n`$ に適用可と明言) | 1994 |
| R3 | Stability 系 | $`\Pi^1_\nu`$-indescribable 基数の階層 | 崩壊関数の階層 | $`\mathrm{KPi}+\forall\rho\,\exists\pi{\gt }\rho\,(\pi \text{ は } \pi^+\text{-stable})`$ | 明示名なし(論文 §の上界) | 2005 (An ordinal analysis of stability; 結果自体は 1995 年に得られたもの) |
| R4 | パラメータ無し $`\Pi^1_2`$-CA 系 | 「強い indescribability を持つ基数」(部分初等埋め込みの逆写像として projection functions をモデル化) | projection functions | $`\mathrm{KPi}+\exists\pi\,(\pi\text{ stable})`$ $`=\Delta^1_2\text{-CA}+\mathrm{BI}+\Pi^1_2\text{-CA}^-`$ (パラメータ無し) | 明示名なし | 2005 (An ordinal analysis of parameter free Π¹₂-comprehension) |
| R5 | 完全 $`\Pi^1_2`$-CA 系(未公刊) | 同上の拡張 | 同上 | $`\mathrm{KP}+\Sigma_1\text{-Sep}`$ $`=\Pi^1_2\text{-CA}+\mathrm{BI}`$ | 概説のみ | 1995 (BSL announcement)。詳細プレプリント *An ordinal representation system for Π¹₂-comprehension and related systems* (urr.ps) は散逸 |

### どれが一番大きいか

- **完全に定義が公刊されている中で最大なのは R4**
  (2005, An ordinal analysis of parameter free Π¹₂-comprehension)。
  R3 (stability) はその下準備であり、3 部作の第 3 部(完全 $`\Pi^1_2`$-CA = R5)は公刊されなかった。
- R5 の表記系そのもの("An ordinal representation system for Π¹₂-comprehension and
  related systems", urr.ps)は Internet Archive 等でも現存が確認できない。
  よって**エビデンスを取れる最大ターゲットは R4(実務上はまず R3)**。

### 強さの順序(まとめ)

```math
\underbrace{\psi_0(\Omega_\omega)}_{\text{2行BMS極限}}
< \psi_{\Omega_1}(\varepsilon_{I+1})
< \underbrace{\psi_{\Omega_1}(\varepsilon_{M+1})}_{R1:\ \mathrm{KPM}}
< \underbrace{\Psi^0_{\Omega_1}(\varepsilon_{K+1})}_{R2:\ \Pi_3\text{-Ref}}
< \underbrace{\cdots}_{R2':\ \Pi_n\text{-Ref}}
< \underbrace{\cdots}_{R3:\ \text{stability}}
< \underbrace{\cdots}_{R4:\ \Pi^1_2\text{-CA}^-}
< \underbrace{\cdots}_{R5:\ \Pi^1_2\text{-CA}}
```

## BMS との位置関係(既知の予想)

[BM4-Analysis](https://docs.google.com/spreadsheets/d/1Y4BV65KNPjJ6uBtBBFYDXKo6PFlmEuowyn39XmLh4MI/edit?usp=sharing)
の各シートとの対応:

| xlsx シート | 到達点 | 必要な表記系 |
|---|---|---|
| To psi(I) | $`\psi(I)`$ | Jäger $`T(J)`$ (R1 の $`\chi`$ で被覆可) |
| To psi(W(2,0)) | $`\psi(\Omega(2,0))`$ (到達不能階層) | R1 の $`\chi`$ 階層 |
| To psi(W_(M+1)) | $`\psi(\Omega_{M+1})`$ | R1: $`T(M)`$ |
| To psi(N) | $`\psi(M(1,0))`$ (hyper-Mahlo 階層) | R1〜R2 中間 |
| To psi(K) | $`\psi(K)`$ | R2: $`T(K)`$ |
| To psi(e(K+1)) | $`\psi(\varepsilon_{K+1})`$ 近傍 | R2: $`T(K)`$ |

注意:

- xlsx の全フロンティアは **3 行 BMS のまま** $`\psi(\varepsilon_{K+1})`$ 相当に達している。
  すなわち 3 行 BMS の極限ですら R2 を超える可能性があり、
  4 行以上・BMS 全体の極限は R3/R4 レベル以上と予想される(正確な位置は未解決)。
- xlsx は有志による解析であり、大きい側には誤りの可能性が大いにある。
  この検証こそが本プロジェクトの LEAN エビデンスの目的である。
