import Lake

open System Lake DSL

package skimmer where version := v!"0.1.0"

require "leanprover-community" / batteries @ git "main"

@[default_target] lean_lib Skimmer where leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_lib SkimmerPlugin where
  globs := #[`SkimmerPlugin.+]
  defaultFacets := #[`lean_lib.shared]
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_lib SkimmerTest where
  globs := #[`SkimmerTest.+]
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_lib SkimmerExtra where
  globs := #[`SkimmerExtra.+]
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_exe write_edits where
  root := `Skimmer.Execute
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_exe working where
  root := `Skimmer.Working.Main
  supportInterpreter := true
  leanOptions := #[⟨`experimental.module, true⟩]

lean_lib WorkingTest where
  globs := #[`WorkingTest.+]
  leanOptions := #[⟨`experimental.module, true⟩]
