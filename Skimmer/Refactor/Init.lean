/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Skimmer.Refactor.Edit
public import Skimmer.AttrUtil
public import Skimmer.LinterWithCleanup.Run
public import Skimmer.AccumulativeLinter

@[expose] public section

open Lean Elab Command

namespace Skimmer

/-- The extension holding all edits produced by any refactor. -/
initialize editExt : PersistentEnvExtension Edit (Array Edit) (Array Edit) ←
  registerPersistentEnvExtension {
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := Array.append
    statsFn edits := f!"{edits.size} edits"
    exportEntriesFnEx _ edits _ := edits
  }

initialize commandRefactor : SimpleAccumulativeLinter Edit (Array Edit) (Array Edit) ←
  registerAndAddSimpleAccumulativeLinterUsingExt editExt {
    produce? stx := do
      let refactorss := commandRefactorAttr.ext.getImportedEntries (← getEnv)
      let mut edits := #[]
      for refactors in refactorss do
        for refactor in refactors do
          let refactor ← unsafe evalConstCheck Refactor ``Refactor refactor
          edits := edits ++ (← refactor stx)
      if edits.isEmpty then return none else return some edits
    submit := sorry -- TODO
  }

namespace Command

structure Refactor where
  name : Name := by exact decl_name%
  run : Syntax → CommandElabM (Array Edit)
deriving Inhabited

/-- We use a linter-like model to make it easier to load these as plugins and access them during linting. -/
initialize refactorsRef : IO.Ref (Array Refactor) ← IO.mkRef #[]

/-- Basically a carbon-copy of `runLinters`. -/
def runRefactors (stx : Syntax) (process : Array Edit → CommandElabM Unit) : CommandElabM Unit := do
  profileitM Exception "refactoring" (← getOptions) do
    withTraceNode `Skimmer.Refactor (fun _ => return m!"running refactors") do
      let refactors ← refactorsRef.get
      unless refactors.isEmpty do
        let mut allEdits := #[]
        for refactor in refactors do
          withTraceNode `Skimmer.Refactor
              (fun _ => return m!"running refactor: {.ofConstName refactor.name}")
              (tag := refactor.name.toString) do
            let savedState ← get
            try
              let edits ← refactor.run stx
              -- don't trace yet in case it mysteriously affects performance somehow
              -- trace[Skimmer.Refactor] "Recorded {edits.size} edit(s):\n{edits}"
              unless edits.isEmpty do
                -- need to check if appending is morre performant, or if allocating an array of arrays and `push`ing is more performant...
                allEdits := allEdits ++
            catch
            | Exception.error ref msg =>
              logException (.error ref m!"refactor {.ofConstName refactor.name} failed: {msg}")
            | ex@(Exception.internal ..) =>
              logException ex
            finally
              modify fun s => { savedState with messages := s.messages, traceState := s.traceState }


-- TODO: rules that apply to any syntax, keyed by syntaxnodekind
