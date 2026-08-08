/-
Test/TransTest.lean — 翻訳 o (Stage A: 1 行領域) の検査

- E1: 代表値の直接検査
- checkAll: コーパス全数の分類保存・後続対応・E2 (順序埋め込み)・E3 相互共終形
- strict bisim: CNF 領域では BMS の展開列と fs の列が (添字 +1 のずれを除いて)
  一致することの確認
- ε₁ では両者が異なる共終列になる (値は同じ) ことの記録
-/
import Evidence.Check
import Evidence.Bisim

namespace Trans.Test
open BMS TM.Term Trans Evidence

-- E1: 1 行領域の代表値
#guard oPr [[0]] = one
#guard oPr [[0],[1]] = omega
#guard oPr [[0],[1],[0],[1]] = add omega omega          -- ω·2
#guard oPr [[0],[1],[1]] = phi zero (ofNat 2)           -- ω²
#guard oPr [[0],[1],[2]] = phi zero omega               -- ω^ω
#guard oPr [[0],[1],[2],[3]] = phi zero (phi zero omega) -- ω^ω^ω
#guard oPr [[0,0],[1,0],[2,0]] = phi zero omega         -- 行 0 のみの 2 行でも同じ

-- コーパス全数検査 (1 行: 深さ 4 幅 3 / 行 0 のみの 2 行: 深さ 3 幅 3)
def c1 : List Matrix := corpus [[0],[1],[2]] 4 3
def c2 : List Matrix := corpus [[0,0],[1,0],[2,0]] 3 3
#guard c1.length ≥ 40
#guard checkAll oPr c1 3 6
#guard checkAll oPr c2 3 6

-- strict bisim: CNF 領域 + ε₀ では展開列と fs 列が一致する
#guard bisim 5 [[0,0],[1,0]] omega 3
#guard bisim 5 [[0,0],[1,1]] (phi one zero) 3
-- ε₁ では一致しない (BMS は ε₀-タワー、fs は ω-タワーで登る。値は同じ):
#guard !(bisim 3 [[0,0],[1,1],[1,1]] (phi one one) 3)

end Trans.Test
