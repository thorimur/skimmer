import Lake
import Lean

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

@[default_target] lean_lib SkimmerHub where
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

section

open Lean

structure EditData where
  edits : System.FilePath
  mdata : System.FilePath
  -- The following have to be pickled into the mdata, in order to cross the subprocess boundary
  -- The artifact consists of both of these together, of course. Can we have subartifacts?
  -- Further on we may want edits to be contributed to by multiple things; will we want to aggregate the mdata on the fly? Probably produce an aggregated mdata via pickle
  -- uri : Lsp.DocumentUri
  -- editLocs   : Array Lsp.Range
  -- reviewLocs : Array Lsp.Range

end

module_facet pickleJar (mod : Module) : EditData := do
  let e ← fetch mod.backend
