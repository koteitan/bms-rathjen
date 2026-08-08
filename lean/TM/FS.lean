/-
TM/FS.lean — 𝔗(M) の基本列 (fundamental sequences)

【重要】[R91] に基本列の定義は無い。ここは本リポジトリの設計上の選択であり、
[R90] の C_κ(α,β) の閉包構造 (何の関数で閉じているか) から共終列を導出する
標準的な方法 (Buchholz 流、p進大好きbot のペア数列論文 §4 と同型) に従う。
E3 (o(M[n]) = (o M)[n]) の検証がこの定義の妥当性テストになる。

構成:
  kindT : 零・後続・極限の分類 (加法末尾が 1 = φ̄00 なら後続)
  predT : 後続の前者
  cofT  : 極限項の共終度マーカー (ω なら可算、Z δ / M なら非可算正則)
  fsT   : 項添字の基本列 t[s] (共終度が非可算正則 π の位置で s < π を代入)
  fsN   : 自然数添字の基本列 t[n] (共終度 ω)

設計の根拠 (各ケース):
  ⊕      : 最後の成分に伝播 (加法の標準)
  ω̄^γ   : γ 後続 → ω̄^{γ'}·n、γ 極限 → ω̄^{γ[·]} (指数に伝播)
  φ̄ a b : [R91] 2.7 の対応 φ̄αβ = φα(β°) に従い、意味論的引数
           β° = β+1 (b が a-不動点形 + 有限、または b=0 ∧ a∈SC) / β (それ以外)
           を復元してから、Veblen 階層の標準基本列
             φ_{α+1}(0)[n]   = φ_α^{(n)}(0)
             φ_α(β+1)[n]     = φ_{α'}^{(n)}(φ_α(β)+1)   (α = α'+1)
             φ_α(β+1)[n]     = φ_{α[n]}(φ_α(β)+1)       (α 極限)
             φ_α(β)[·]       = φ_α(β[·])                 (β 極限)
             φ_0(β+1)[n]     = ω^β · n
           を適用する。
  ψ κ α : C-閉包の共終列。
           α = 0    → 種 seed(κ) から x ↦ φ_x(0) を反復 (Γ-閉包)。
                      seed(Z0) = 1、seed(Z(δ+1)) = Zδ + 1
                      (κ 未満の最大の正則項より上で φ-閉包を取る)。
                      δ 極限のときは ψ_{Zδ}(0)[·] = Z(δ[·])
                      (Z の像が共終: 正則の谷間を φ-閉包が越えないため)。
           α 後続   → ψκα' + 1 から x ↦ φ_x(0) を反復。
           α 極限, cof α < κ → ψ κ (α[·]) (添字をそのまま通す)。
           α 極限, cof α ≥ κ → 対角化: t[0] = ψκ(α[0]),
                      t[n+1] = ψκ(α[t[n]]) (添字に自分自身の前項を使う)。
  Z δ, M : 正則。fsT は恒等 (κ[s] = s)、fsN は未定義 (junk 0)。

fsN が junk 0 を返すのは「可算共終度でない項」に誤って適用した場合のみ。
行ごとの検査 (E3 + inT) がその混入を検出する。
-/
import TM.NF

namespace TM
namespace Term

/-- 零・後続・極限の分類 -/
inductive KindT | isZero | isSucc | isLim
deriving DecidableEq, Repr

/-- 分類: 加法表示の末尾が 1 (= φ̄00) なら後続 -/
def kindT (t : Term) : KindT :=
  match t with
  | zero => .isZero
  | _ => if (toList t).getLast? == some one then .isSucc else .isLim

/-- 後続 t = s + 1 の前者 s (後続以外には zero) -/
def predT (t : Term) : Term :=
  let l := toList t
  if l.getLast? == some one then ofList l.dropLast else zero

/-- g が a-不動点形か: g ∈ SC ∧ a < g、または g = φ̄cδ ∧ a < c ([R91] 2.6(vi)) -/
def isFP (a g : Term) : Bool :=
  (g.isSC && lt a g) ||
  (match g with
   | phi c _ => lt a c
   | _ => false)

/-- φ̄ a b の意味論的引数が b+1 (後続) になるか ([R91] 2.7 の場合分け) -/
def phiShifted (a b : Term) : Bool :=
  isFP a (splitFin b).1 || (b == zero && a.isSC)

/-- t · n (t を n 個並べた形式和; t ∈ AP を前提) -/
def mulNat (t : Term) (n : Nat) : Term := ofList (List.replicate n t)

/-- x ↦ φ_c(x) の n 回反復 (base から) -/
def iterPhiAt (c base : Term) : Nat → Term
  | 0 => base
  | n + 1 => phiNF c (iterPhiAt c base n)

/-- x ↦ φ_x(0) の n 回反復 (base から): Γ-閉包の共終列 -/
def iterGamma (base : Term) : Nat → Term
  | 0 => base
  | n + 1 => phiNF (iterGamma base n) zero

/-- 極限項の共終度マーカー: omega (可算) / Z δ / M (非可算正則) -/
def cofT : Term → Term
  | M => M
  | Z d => Z d
  | add _ b => cofT b
  | omg g => if kindT g == .isSucc then omega else cofT g
  | phi a b =>
    if phiShifted a b || kindT b == .isSucc then
      -- 意味論的引数が後続 → 共終度は a 側で決まる
      if kindT a == .isLim then cofT a else omega
    else if kindT b == .isLim then cofT b
    else -- b = 0 (a ≠ 0, a ∉ SC)
      if kindT a == .isLim then cofT a else omega
  | psi k a =>
    match kindT a with
    | .isLim => let p := cofT a; if lt p k then p else omega
    | _ => omega
  | _ => omega   -- zero・後続には使わない

/-- 項添字の基本列 t[s] (cofT t が非可算正則 π のとき、s < π を想定) -/
def fsT : Term → Term → Term
  | add a b, s => plus a (fsT b s)
  | omg g, s => omegaNF (fsT g s)      -- γ 極限。境界 (指数 = M 等) は ω^ の縮約で処理
  | phi a b, s =>
    if phiShifted a b || kindT b == .isSucc then
      -- 後続引数: 共終度は a 側 (a 極限・非可算)
      let c := if phiShifted a b then b else predT b
      phiNF (fsT a s) (plus (phiNF a c) one)
    else if kindT b == .isLim then phiNF a (fsT b s)
    else phiNF (fsT a s) zero          -- b = 0, a 極限
  | psi k a, s => psi k (fsT a s)      -- cof α < κ の伝播
  | Z _, s => s                        -- 正則: κ[s] = s
  | M, s => s
  | _, _ => zero                       -- junk (使われない)

/-- ψκ0 の共終列の種: κ 未満の最大の正則項の次 -/
def psiSeed : Term → Term
  | Z zero => one                      -- Ω の下に正則項は無い
  | Z d =>
    match kindT d with
    | .isSucc => plus (Z (predT d)) one
    | _ => zero                        -- δ 極限は fsN 側で Z(δ[n]) を使う
  | _ => zero

/-- 自然数添字の基本列 t[n] (cofT t = ω を想定) -/
def fsN : Term → Nat → Term
  | add a b, n => plus a (fsN b n)
  | omg g, n =>
    (match kindT g with
     | .isSucc => mulNat (omegaNF (predT g)) n   -- ω̄^{γ'+1}[n] = ω^{γ'}·n
     | _ => omegaNF (fsN g n))                   -- 指数に伝播 (境界は ω^ の縮約で処理)
  | phi a b, n =>
    if phiShifted a b || kindT b == .isSucc then
      -- 意味論的引数が後続 c+1: base = φ_a(c) + 1
      let c := if phiShifted a b then b else predT b
      let base := plus (phiNF a c) one
      match kindT a with
      | .isZero => mulNat (omegaNF c) n          -- ω^{c+1}[n] = ω^c · n
      | .isSucc => iterPhiAt (predT a) base n    -- φ_{a'}^{(n)}(base)
      | .isLim => phiNF (fsN a n) base           -- φ_{a[n]}(base)
    else if kindT b == .isLim then phiNF a (fsN b n)
    else
      -- b = 0 (a ≠ 0, a ∉ SC): φ_a(0)
      (match kindT a with
       | .isSucc => iterPhiAt (predT a) zero n
       | .isLim => phiNF (fsN a n) zero
       | .isZero => zero)                        -- φ̄00 = 1 は後続 (来ない)
  | psi k a, n =>
    (match kindT a with
     | .isZero =>
       (match k with
        | Z d =>
          (match kindT d with
           | .isLim => Z (fsN d n)               -- ψ_{Zδ}0[n] = Z(δ[n]) (δ 極限)
           | _ => iterGamma (psiSeed k) n)       -- Γ-閉包
        | _ => zero)
     | .isSucc => iterGamma (plus (psi k (predT a)) one) n
     | .isLim =>
       let p := cofT a
       if p == omega then psi k (fsN a n)        -- 可算共終度: そのまま伝播
       else if lt p k then zero                  -- cof α < κ: fsN の対象外 (junk)
       else
         -- 対角化: t[0] = ψκ(α[0]), t[n+1] = ψκ(α[t[n]])
         (match n with
          | 0 => psi k (fsT a zero)
          | m + 1 => psi k (fsT a (fsN (psi k a) m))))
  | _, _ => zero   -- zero / 後続 / Z / M には使わない
  termination_by t n => (sizeOf t, n)
  decreasing_by all_goals simp_wf <;> omega

end Term
end TM
