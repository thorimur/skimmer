/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Skimmer.Extension

@[expose] public section

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot) ["/Users/thomas/LT2026/Demo"]
  enableInitializersExecution
  let env ← importModules #[{module := `Demo}] {} (loadExts := true)
  executeEdits env `Demo
