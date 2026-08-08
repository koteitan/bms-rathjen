import Lake
open Lake DSL

package «pss-rathjen» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-- BMS 側: 行列・順序・展開・標準形 -/
@[default_target] lean_lib BMS where
  srcDir := "."
  globs := #[Glob.andSubmodules `BMS]

/-- Rathjen T(M) 側: 項・順序・正規形・基本列 -/
@[default_target] lean_lib TM where
  srcDir := "."
  globs := #[Glob.andSubmodules `TM]

/-- 翻訳関数 o : BMS → T(M) (module 名は Trans、lib 宣言名は core の Trans と衝突するため別名) -/
@[default_target] lean_lib TransLib where
  srcDir := "."
  globs := #[Glob.andSubmodules `Trans]

/-- 対応表の行データベースと行ごとの補題 (E1/E3) -/
@[default_target] lean_lib Rows where
  srcDir := "."
  globs := #[Glob.andSubmodules `Rows]

/-- 一般定理 (E2 順序埋め込み、G 構造定理、MT) -/
@[default_target] lean_lib Evidence where
  srcDir := "."
  globs := #[Glob.andSubmodules `Evidence]

/-- スモークテストと crosscheck 用 CLI -/
@[default_target] lean_lib Test where
  srcDir := "."
  globs := #[Glob.andSubmodules `Test]

/-- 表生成: 行 DB → table/r1-tm.md -/
lean_exe gentable where
  root := `Main

/-- yaBMS との突き合わせ用 CLI (標準入力で expand/cmp を受ける) -/
lean_exe bmscli where
  root := `Test.CLI
