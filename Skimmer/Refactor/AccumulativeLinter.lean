import Skimmer.Refactor.Attr
import Skimmer.Accumulator.Defs

open Lean


def commandRefactorDescr : AccumulatorDescr (Array Edit) Edit SourceIndexedArray IO.Ref where
  name := `commandRefactor
  recordInLinter? stx := do
    let refactorss := commandRefactorAttr.ext.getImportedEntries (← getEnv)
    let mut edits := #[]
    for refactors in refactorss do
      for refactor in refactors do
        let refactor ← unsafe evalConstCheck Refactor ``Refactor refactor
        edits := edits ++ (← refactor stx)
    if edits.isEmpty then return none else return some edits
  append a edits := a ++ edits.2
  exportEntriesFnEx _ a _ := a.sortEdits
  interactiveTrackingScope := .upToCommandEndWithTrailing

initialize commandRefactor : Accumulator (Array Edit) Edit Edit SourceIndexedArray IO.Ref ←
  commandRefactorDescr.registerAccumulator
