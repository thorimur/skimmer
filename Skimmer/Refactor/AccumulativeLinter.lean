/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Skimmer.Refactor.Attr
import Skimmer.AccumulativeLinter

open Lean

initialize commandRefactor : SimpleAccumulativeLinter Edit (Array Edit) (Array Edit) ←
  registerAndAddSimpleAccumulativeLinter {
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := Array.append
    produce? stx := do
      let refactorss := commandRefactorAttr.ext.getImportedEntries (← getEnv)
      let mut edits := #[]
      for refactors in refactorss do
        for refactor in refactors do
          let refactor ← unsafe evalConstCheck Refactor ``Refactor refactor
          edits := edits ++ (← refactor stx)
      if edits.isEmpty then return none else return some edits
    exportEntriesFnEx _ edits _ := edits.sortEdits
  }
