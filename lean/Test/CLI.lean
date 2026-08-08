/-
Test/CLI.lean — yaBMS との突き合わせ用 CLI (lean_exe bmscli)

標準入力から 1 行 1 コマンドを読む:
  expand <matrix> <n>   → 展開結果を "(0,0)(1,0)" 形式で出力 (未定義なら "undefined")
  cmp <m0> <m1>         → 1 / 0 / -1  (m0 > m1 / == / <)   yaBMS -c と同じ
空行列は "" で表す。出力は 1 行 1 応答。
-/
import BMS

open BMS

def runLine (line : String) : String :=
  let ws := ((trimS line).splitOn " ").filter (· ≠ "")
  match ws with
  | ["expand", ms, ns] =>
    match parseMatrix ms, ns.toNat? with
    | some M, some n =>
      match expand? M n with
      | some R => showMatrix R
      | none => "undefined"
    | _, _ => "parse-error"
  | ["expand", ns] =>
    -- 空行列の展開: "expand <n>" の形で受ける
    match ns.toNat? with
    | some _ => "undefined"
    | none => "parse-error"
  | ["cmp", m0, m1] =>
    match parseMatrix m0, parseMatrix m1 with
    | some a, some b =>
      match cmpM a b with
      | .gt => "1"
      | .eq => "0"
      | .lt => "-1"
    | _, _ => "parse-error"
  | [] => ""
  | _ => "parse-error"

partial def loop (h : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then
    pure ()  -- EOF
  else
    -- 1 入力行につき必ず 1 出力行 (空行列の展開結果は空行)
    IO.println (runLine line)
    loop h

def main : IO Unit := do
  loop (← IO.getStdin)
