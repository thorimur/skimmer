import Lean

open Lean

def validateHasExactlyTypeNoSorry (expectedType : Expr) (decl : Name) : AttrM Unit := do
  let d ← getAsyncConstInfo decl (skipRealize := true)
  let { type .. } := d.sig.get
  unless type == expectedType do
    throwError "Expected type to be exactly\
      {indentD <| expectedType}\n, got\
      {indentD type}"
  let some val := d.constInfo.get.value? | throwError "`{decl}` has no value"
  if type.hasSorry || val.hasSorry then
    throwError "`{decl}` uses `sorry`"

@[inline] def Lean.PersistentEnvExtension.getImportedEntries [Inhabited σ]
    (ext : PersistentEnvExtension α β σ) (env : Environment)
    (asyncMode : EnvExtension.AsyncMode := ext.toEnvExtension.asyncMode) : Array (Array α) :=
  (ext.toEnvExtension.getState env asyncMode).importedEntries
