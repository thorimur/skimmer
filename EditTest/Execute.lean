import EditTest.Extension

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← getBuildDir)
  enableInitializersExecution
  let env ← importModules #[{module := `EditTest}] {} (loadExts := true)
  executeEdits env `EditTest
