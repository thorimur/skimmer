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
public section

open Lean Elab Command

namespace Skimmer

namespace Command

structure Refactor where
  name : Name := by exact decl_name%
  run : Syntax → CommandElabM (Array Edit)
deriving Inhabited

/-- We use a linter-like model to make it easier to load these as plugins and access them during linting. -/
initialize refactorsRef : IO.Ref (Array Refactor) ← IO.mkRef #[]

/-- Basically a carbon-copy of `runLinters`. -/
def runRefactors (stx : Syntax) : CommandElabM (Array Edit) := do
  profileitM Exception "refactoring" (← getOptions) do
    withTraceNode `Skimmer.Refactor (fun _ => return m!"running refactors") do
      let refactors ← refactorsRef.get
      if refactors.isEmpty then return #[] else
        let mut allEdits := #[]
        for refactor in refactors do

          let savedState ← get
          try
            -- TODO: really, this should be on the outside, but it interferes with `let mut`
            let edits ← withTraceNode `Skimmer.Refactor
                (fun _ => return m!"running refactor: {.ofConstName refactor.name}")
                (tag := refactor.name.toString) do
              -- don't trace yet in case it mysteriously affects performance somehow
              -- trace[Skimmer.Refactor] "Recorded {edits.size} edit(s):\n{edits}"
              let edits ← refactor.run stx
              pure edits

            unless edits.isEmpty do
              -- need to check if appending is more performant, or if allocating an array of arrays and `push`ing is more performant...
              allEdits := allEdits ++ edits

          catch
          | Exception.error ref msg =>
            logException (.error ref m!"refactor {.ofConstName refactor.name} failed: {msg}")
          | ex@(Exception.internal ..) =>
            logException ex
          finally
            modify fun s => { savedState with messages := s.messages, traceState := s.traceState }
        return allEdits

/-- Runs all refactors. -/
initialize refactorLinter : SimpleAppendLinter Edit ←
  SimpleAppendLinter.registerAndAddUsingExt editExt { produce := runRefactors }

-- TODO: rules that apply to any syntax, keyed by syntaxnodekind
