/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Skimmer.Refactor.Edit
public import Skimmer.AttrUtil

@[expose] public section

open Lean Elab Command

namespace Skimmer

abbrev Refactor := Syntax → CommandElabM (Array Edit)

initialize editExt : PersistentEnvExtension Edit (Array Edit) (Array Edit) ←
  registerPersistentEnvExtension {
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := Array.append
    statsFn edits := f!"{edits.size} edits"
    exportEntriesFnEx _ edits _ := edits
  }

-- TODO: make scoped, allow erased, etc.
initialize commandRefactorAttr : TagAttribute ← (registerTagAttribute
  `command_refactor
  "Stores a refactoring to be applied by the refactoring linter to whole commands."
  (applicationTime := .afterCompilation)
  (validateHasExactlyTypeNoSorry <| mkConst ``Refactor)
)

-- TODO: rules that apply to any syntax, keyed by syntaxnodekind
