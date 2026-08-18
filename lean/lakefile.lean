import Lake
open Lake DSL

package «bms-rathjen» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-- The BMS side: matrices, order, expansion, standard form. -/
@[default_target] lean_lib BMS where
  srcDir := "."
  globs := #[Glob.andSubmodules `BMS]

/-- The Rathjen T(M) side: terms, order, normal forms, fundamental sequences. -/
@[default_target] lean_lib TM where
  srcDir := "."
  globs := #[Glob.andSubmodules `TM]

/-- The translation o : BMS → T(M).  The modules are `Trans.*`; the library is named
    differently because `Trans` clashes with the core declaration of that name. -/
@[default_target] lean_lib TransLib where
  srcDir := "."
  globs := #[Glob.andSubmodules `Trans]

/-- The row database of the table and the per-row lemmas (E1/E3). -/
@[default_target] lean_lib Rows where
  srcDir := "."
  globs := #[Glob.andSubmodules `Rows]

/-- The general theorems (E2 order embedding, the G structure theorems, MT). -/
@[default_target] lean_lib Evidence where
  srcDir := "."
  globs := #[Glob.andSubmodules `Evidence]

/-- Smoke tests and the CLI used for cross-checking. -/
@[default_target] lean_lib Test where
  srcDir := "."
  globs := #[Glob.andSubmodules `Test]

/-- Table generation: row database → table/table-r1.md. -/
lean_exe gentable where
  root := `Main

/-- The CLI used to cross-check against yaBMS (reads expand/cmp on standard input). -/
lean_exe bmscli where
  root := `Test.CLI

/-- `scripts/or`'s Lean half: one matrix on the command line → its 𝔗(M) notation. -/
lean_exe orcli where
  root := `Test.ORCLI

/-- `scripts/pss2bp`'s Lean half: one matrix → its Buchholz term (`oRB`).  This is
    OUR port, not the reference implementation of the same name; see Test/BPCLI.lean. -/
lean_exe bpcli where
  root := `Test.BPCLI
