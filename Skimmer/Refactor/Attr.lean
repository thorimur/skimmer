/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Skimmer.Edit
import Skimmer.AttrUtil

open Lean Elab Command

abbrev Refactor := Syntax → CommandElabM (Array Edit)

-- TODO: make scoped, allow erased, etc.
initialize commandRefactorAttr : TagAttribute ← (registerTagAttribute
  `command_refactor
  "Stores a refactoring to be applied by the refactoring linter to whole commands."
  (applicationTime := .afterCompilation)
  (validateHasExactlyTypeNoSorry <| mkConst ``Refactor)
)

-- TODO: rules that apply to any syntax, keyed by syntaxnodekind
