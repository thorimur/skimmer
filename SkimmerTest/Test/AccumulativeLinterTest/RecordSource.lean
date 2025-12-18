/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Skimmer.AccumulativeLinter
import Skimmer.LinterWithCleanup.RangeRecord
import Skimmer.LinterWithCleanup.Defs
import Lean

public meta section

open Lean

structure TestResult where
  module              : Name
  reconstructedSource : String
  source              : String
  fragments           : Array Substring.Raw
  equal               : Bool := reconstructedSource == source
deriving Inhabited, Repr

def Bool.toEmoji : Bool → String
| true => checkEmoji
| false => crossEmoji

instance : ToMessageData TestResult where
  toMessageData
  | { module, reconstructedSource, source, equal, fragments } =>
    m!"{equal.toEmoji}{module}" ++ if equal then .nil else
    m!"reconstructed:
    -----
    {reconstructedSource}
    -----
    original:
    -----
    {source}
    -----
    {fragments}"

initialize recordSourceLinter :
    AccumulativeLinter TestResult (Array TestResult) (Array TestResult)
      Substring.Raw (Array Substring.Raw) TestResult ←
  AccumulativeLinter.registerAndAdd {
    init := #[]
    add s a := a.push s
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := Array.append
    persist ext a env := ext.addEntry env a
    produce stx := do
      let range ← stx.getRangeForRecordRange!
      let source := (← getFileMap).source
      return ⟨source, range.start, range.stop⟩
    produceOnHeader? := some fun ws stx => do
      let range ← stx.getRangeForRecordRange! (isHeader := true)
      let source := (← getFileMap).source
      return ⟨source, range.start, range.stop⟩
    submit a := do
      let mut reconstructedSource := ""
      let module ← getMainModule
      for s in a.qsort (·.startPos < ·.startPos) do
        if reconstructedSource.rawEndPos == s.startPos then
          reconstructedSource := reconstructedSource ++ s.toString
        else
          return #[{
            module
            reconstructedSource
            source := (← getFileMap).source
            fragments := a
          }]
      return #[{
        module
        reconstructedSource
        source := (← getFileMap).source
        fragments := a
      }]
    exportEntriesFnEx _ n _ := n
  }
