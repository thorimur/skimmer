import Lean

/-!
# Cleanup functionality

Provides an extensible way to run "cleanups" ("closeouts"?) at the end of every lean file. We do this by hijacking the elaboration of the end-of-input command that appears at the end of every file. Note that this usually just elaborates to `pure ()` (see `elabEoi`), so we are not preventing any crucial functionality.

Each cleanup has type `CommandElab`; the input `stx` is that of the `eoi` node itself.

TODO: make this scoped
-/

open Lean Meta Elab Command

initialize cleanupAttr : TagAttribute ← (registerTagAttribute
  `cleanup
  "Cleanup declarations which are run at the end of each file."
  (applicationTime := .afterCompilation)
  (fun decl => do
    let d ← getAsyncConstInfo decl (skipRealize := true)
    let { type .. } := d.sig.get
    unless type == Expr.const ``CommandElab [] do
      throwError "Expected type to be exactly\
        {indentD <| Expr.const ``CommandElab []}\ni.e. `Syntax → CommandElabM Unit`, got\
        {indentD type}"
    let some val := d.constInfo.get.value? | throwError "`{decl}` has no value"
    if type.hasSorry || val.hasSorry then
      throwError "`{decl}` uses `sorry`"
  )
)
