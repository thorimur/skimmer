import EditTest.Edit
import EditTest.AttrUtil

open Lean Elab Command

abbrev Refactor := Syntax → CommandElabM (Array Edit)

-- TODO: make scoped, allow erased, etc.
initialize refactorRulesExt : TagAttribute ← (registerTagAttribute
  `refactorRules
  "Stores refactor rules to be applied by the refactoring linter."
  (applicationTime := .afterCompilation)
  (validateHasExactlyTypeNoSorry <| mkConst ``Refactor)
)
