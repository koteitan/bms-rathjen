/-
BMS/Basic.lean — バシク行列の表現と基本操作

出典: Koteitan「バシク行列の数式的定義」(巨大数研究 Wiki ユーザーブログ)。
以下のコメントで「数式的定義」と呼ぶ。BMS のバージョンは BM4。

行列 S = S_0 S_1 ... S_{X-1} を列のリストで表す。
列 S_x = (S_{x0}, ..., S_{x(Y-1)}) は上の行から下の行への成分リスト。
-/

namespace BMS

/-- 列: 上の行 (行番号 0) から下の行への成分リスト -/
abbrev Col := List Nat

/-- 行列: 左から右への列のリスト -/
abbrev Matrix := List Col

/-- 全列の高さが h で揃っている -/
def WF (h : Nat) (M : Matrix) : Prop := ∀ c ∈ M, c.length = h

/-- 成分 S_{xy}。範囲外は 0 (標準形の範囲では参照しない)。 -/
def ent (M : Matrix) (x y : Nat) : Nat := (M.getD x []).getD y 0

/-- 初期行列 (0,...,0)(1,...,1) (高さ h)。表の起点。 -/
def init (h : Nat) : Matrix := [List.replicate h 0, List.replicate h 1]

/-- "(0,0,0)(1,1,1)" 形式の表示 (yaBMS と同じ書式) -/
def showMatrix (M : Matrix) : String :=
  String.join (M.map fun c => "(" ++ String.intercalate "," (c.map toString) ++ ")")

/-- 空白除去 (v4.30: trimAscii は Slice を返すので String に戻す) -/
def trimS (s : String) : String := s.trimAscii.toString

/-- "(0,0,0)(1,1,1)" 形式の読み取り。空文字列は空行列。 -/
def parseMatrix (s : String) : Option Matrix :=
  let parts := (((trimS s).splitOn ")").map trimS).filter (· ≠ "")
  parts.mapM fun p => do
    guard (p.startsWith "(")
    ((trimS (p.drop 1).toString).splitOn ",").mapM (fun w => (trimS w).toNat?)

end BMS
