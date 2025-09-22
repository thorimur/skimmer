import Skimmer.Extension

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← getBuildDir)
  enableInitializersExecution
  let env ← importModules #[{module := `Skimmer}] {} (loadExts := true)
  executeEdits env `Skimmer
